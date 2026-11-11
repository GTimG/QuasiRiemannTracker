"""Fetch the signed shards of the submission build cache before any candidate code executes."""
from pathlib import Path
import json, subprocess, sys, tempfile
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from cache_release import KEY, authenticate, download, fetch_index, fetch_shards
from standard.build_cache import build_inputs, compatibility_error, digest


def main():
    out = Path('verification').resolve()
    profile_path = out/'profile.json'
    profile = json.loads(profile_path.read_text())
    profile.pop('candidate_cache', None)
    status = {'status': 'miss'}
    try:
        prepared = out/'prepared'
        inputs = build_inputs(json.loads((prepared/'contract.json').read_text()), profile,
            json.loads((prepared/'libraries.json').read_text()), json.loads((out/'tool-pins.json').read_text()))
        (out/'build-cache-inputs.json').write_text(json.dumps(inputs, sort_keys=True)+'\n')
        status.update(worker_environment=inputs['environment'])
        with tempfile.TemporaryDirectory(dir=out, prefix='build-index-') as tmp:
            index = fetch_index(Path(tmp), fetch=download, verify=authenticate)
        if index is None:
            raise ValueError('No build cache is published yet')
        status.update(cache_environment=index.get('environment'))
        if reason := compatibility_error(index, inputs):
            raise ValueError(reason)
        # Download only the shards that hold a module this build can reuse.
        wanted = {name for name, shard in index['shards'].items()
                  if any(inputs['modules'].get(m) == k for m, k in shard['modules'].items())}
        matches = sum(index['shards'][n]['modules'].get(m) == k
                      for n in wanted for m, k in inputs['modules'].items())
        status.update(matching_modules=matches, required_modules=len(inputs['modules']),
                      shards=sorted(wanted))
        if not wanted:
            raise ValueError('Compiler and libraries match; no submitted module matches the cache')
        directory = out/'build-cache'
        directory.mkdir(exist_ok=True)
        shards = fetch_shards(index, wanted, directory, fetch=download)
        profile['candidate_cache'] = {'shards': shards, 'signer': digest(KEY)}
        status.update(status='hit')
        print(f'Signed build cache: {matches}/{len(inputs["modules"])} modules from '
              f'{len(shards)} shards; checking archives during replay', flush=True)
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as error:
        status['reason'] = f'{type(error).__name__}: {error}'
        print(f'Build cache unavailable ({status["reason"]}); compiling submitted source', flush=True)
    (out/'build-cache-status.json').write_text(json.dumps(status, indent=2)+'\n')
    profile_path.write_text(json.dumps(profile, indent=2)+'\n')


if __name__ == '__main__':
    main()
