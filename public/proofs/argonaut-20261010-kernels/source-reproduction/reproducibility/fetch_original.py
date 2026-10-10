"""Download the exact Argonaut release; no build scripts are executed."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, io, json, stat, urllib.request, zipfile

HERE = Path(__file__).resolve().parents[1]
PIN = json.loads((HERE / 'source-provenance.json').read_text())
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=True)
if any(args.output.iterdir()):
    parser.error('Output must be empty.')
with urllib.request.urlopen(PIN['archive_url'], timeout=120) as response:
    data = response.read(PIN['archive_bytes'] + 1)
if len(data) != PIN['archive_bytes'] or hashlib.sha256(data).hexdigest() != PIN['archive_sha256']:
    raise SystemExit('Archive size or SHA256 mismatch; no files extracted.')
with zipfile.ZipFile(io.BytesIO(data)) as archive:
    members = archive.infolist()
    if len(members) != 12 or sum(x.file_size for x in members) > 50 * 1024 * 1024:
        raise SystemExit('Unexpected outer archive layout.')
    for entry in members:
        name = PurePosixPath(entry.filename)
        kind = stat.S_IFMT(entry.external_attr >> 16)
        if name.is_absolute() or '..' in name.parts or '\\' in entry.filename or kind not in (0, stat.S_IFREG, stat.S_IFDIR):
            raise SystemExit('Unsafe archive entry.')
        output = args.output.joinpath(*name.parts)
        if entry.is_dir():
            output.mkdir(parents=True, exist_ok=True)
        else:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(archive.read(entry))
print('Exact release restored; follow its BUILD.md. No compiler or script was run.')
