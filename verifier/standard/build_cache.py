"""Authenticated compilation archives, adapted from PR #35 for shared modules."""
from pathlib import Path
import hashlib, io, json, re, shutil, tarfile, tempfile

MAX_BYTES = 4 * 1024 ** 3
MAX_FILES = 50000
SUFFIXES = ('.olean', '.olean.private', '.olean.server')
MODULE = re.compile(r'(?:Candidate|Submissions)(?:\.[A-Za-z_][A-Za-z0-9_]*)+')
SHARED = re.compile(r'Submissions(?:\.[A-Za-z_][A-Za-z0-9_]*){2,}')
# Bump when changing compiler flags, exported products or module build semantics.
RECIPE = 'lean-module-o-private-server-v1'


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def hash_json(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def build_inputs(contract, profile, inventory, tools):
    # Flatten the search path, preserving first-match resolution. Paths and
    # package grouping vary between the server and hosted workers. Only compiler
    # products affect imports; Lake traces and editor indexes are workspace data.
    libraries = [str(Path(p)).rstrip('/')+'/' for p in profile['libraries']]
    products = [(str(Path(filename)), sha) for filename, sha in sorted(inventory.items())
                if filename.endswith((*SUFFIXES, '.so', '.ir', '.ir.sig'))]
    normalized = {}
    for lib in libraries:
        for filename, sha in products:
            if filename.startswith(lib):
                normalized.setdefault(filename[len(lib):], sha)
    if not normalized:
        raise ValueError('Empty build dependency inventory')
    environment = hash_json({'recipe': RECIPE, 'compiler': tools['source_lean'],
                             'platform': 'linux-x86_64', 'libraries': normalized})
    order = contract['build_order']
    deps = contract.get('module_dependencies', {m:order[max(0, i-1):i] for i,m in enumerate(order)})
    keys = {}
    if set(order) != set(deps) or len(set(order)) != len(order):
        raise ValueError('Invalid cache module graph')
    # prepare.mjs supplies a dependency-first topological ordering.
    for module in order:
        if not MODULE.fullmatch(module) or any(d not in keys for d in deps[module]):
            raise ValueError('Invalid cache module ordering')
        source = contract['source_files']['src/'+module.replace('.', '/')+'.lean']
        keys[module] = hash_json({'environment': environment, 'module': module, 'source': source,
                                  'dependencies': {d:keys[d] for d in sorted(deps[module])}})
    return {'schema_version': 2, 'environment': environment, 'modules': keys,
            'compiler': tools['source_lean'], 'libraries': normalized}


def approved_names(inputs):
    if inputs.get('schema_version') != 2 or not isinstance(inputs.get('modules'), dict):
        raise ValueError('Invalid build cache schema')
    if not all(MODULE.fullmatch(m) and re.fullmatch('[a-f0-9]{64}', k)
               for m,k in inputs['modules'].items()):
        raise ValueError('Invalid cache module identity')
    return {m.replace('.', '/')+suffix for m in inputs['modules'] for suffix in SUFFIXES}


def compatibility_error(cached, inputs):
    if cached.get('environment') != inputs['environment']:
        details = []
        if 'compiler' in cached and cached['compiler'] != inputs['compiler']:
            details.append('source compiler differs')
        if 'libraries' in cached:
            previous, current = cached['libraries'], inputs['libraries']
            for label, names in [
                ('worker-only library files', current.keys() - previous.keys()),
                ('cache-only library files', previous.keys() - current.keys()),
                ('changed library files', {n for n in previous.keys() & current.keys()
                                           if previous[n] != current[n]}),
            ]:
                if names:
                    details.append(f'{len(names)} {label}: '+', '.join(sorted(names)[:5]))
        return 'Build cache compiler or libraries differ'+(': '+'; '.join(details) if details else
            f' (cache {cached.get("environment")}, worker {inputs["environment"]})')
    return None


def pack_cache(library, archive, inputs):
    allowed = approved_names(inputs)
    files, total = {}, 0
    for path in sorted(library.rglob('*')):
        if path.is_symlink():
            raise ValueError('Symlink in compiled submission')
        if path.is_dir():
            continue
        name = path.relative_to(library).as_posix()
        if name not in allowed or not path.is_file():
            raise ValueError('Unexpected compiled submission file')
        total += path.stat().st_size
        if total > MAX_BYTES or len(files) >= MAX_FILES - 1:
            raise ValueError('Compiled submission cache exceeds size limits')
        files[name] = digest(path)
    required = {m.replace('.', '/')+'.olean' for m in inputs['modules']}
    if not required.issubset(files):
        raise ValueError('Compiled submission cache is incomplete')
    manifest = json.dumps({'inputs': inputs, 'files': files}, sort_keys=True).encode()
    archive.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, 'w:gz', compresslevel=1) as output:
        entry = tarfile.TarInfo('manifest.json')
        entry.size = len(manifest)
        output.addfile(entry, io.BytesIO(manifest))
        for name in files:
            output.add(library/name, arcname=name, recursive=False)


def restore_cache(archive, library, inputs):
    """Authenticate externally first. Stage validated outputs before publishing."""
    approved_names(inputs)
    if archive.stat().st_size > MAX_BYTES:
        raise ValueError('Compiled submission cache exceeds size limits')
    with tarfile.open(archive, 'r:gz') as source:
        members, total = {}, 0
        for member in source:
            if member.name in members or not member.isfile() or member.size < 0:
                raise ValueError('Invalid compiled submission cache member')
            total += member.size
            if total > MAX_BYTES or len(members) >= MAX_FILES:
                raise ValueError('Compiled submission cache exceeds size limits')
            members[member.name] = member
        entry = members.pop('manifest.json', None)
        if entry is None or entry.size > 16 * 1024 * 1024:
            raise ValueError('Missing or oversized build cache manifest')
        manifest = json.load(source.extractfile(entry))
        cached = manifest['inputs']
        allowed = approved_names(cached)
        if reason := compatibility_error(cached, inputs):
            raise ValueError(reason)
        if set(manifest['files']) != set(members) or not set(members) <= allowed:
            raise ValueError('Build cache inventory differs')
        required = {m.replace('.', '/')+'.olean' for m in cached['modules']}
        if not required.issubset(members):
            raise ValueError('Compiled submission cache is incomplete')
        selected = {m for m,k in inputs['modules'].items() if cached['modules'].get(m) == k}
        names = {m.replace('.', '/')+s for m in selected for s in SUFFIXES}
        # No output becomes available to Lean until every selected file passes.
        library.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=library.parent, prefix='cache-stage-') as tmp:
            stage = Path(tmp)
            for name in sorted(names & members.keys()):
                output = stage/name
                output.parent.mkdir(parents=True, exist_ok=True)
                with source.extractfile(members[name]) as incoming, output.open('xb') as outgoing:
                    shutil.copyfileobj(incoming, outgoing, length=1024*1024)
                if digest(output) != manifest['files'][name]:
                    raise ValueError('Compiled submission cache checksum differs')
                output.chmod(0o444)
            for name in sorted(names & members.keys()):
                target = library/name
                if target.exists() or target.is_symlink():
                    raise ValueError('Build cache destination already exists')
            for name in sorted(names & members.keys()):
                target = library/name
                target.parent.mkdir(parents=True, exist_ok=True)
                (stage/name).rename(target)
        return selected


def shard_of(module):
    """Shared modules live under Submissions.<submission>.*; one shard each."""
    if not SHARED.fullmatch(module):
        raise ValueError('Only shared submission modules are cached')
    return '.'.join(module.split('.')[:2])


def restore_shards(cache, library, inputs):
    """Restore authenticated shards; shards hold disjoint modules."""
    selected = set()
    for shard in cache['shards']:
        archive = Path(shard['path'])
        if digest(archive) != shard['sha256']:
            raise ValueError('Authenticated build cache changed')
        selected |= restore_cache(archive, library, inputs)
    return selected
