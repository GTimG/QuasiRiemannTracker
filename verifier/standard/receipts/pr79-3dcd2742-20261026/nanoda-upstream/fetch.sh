set -euo pipefail
mkdir -p /work/home /work/source /work/evidence
exec > >(tee /work/evidence/fetch.log) 2>&1
curl --fail --location --retry 3 --proto '=https' --tlsv1.2 https://codeload.github.com/ammkrn/nanoda_lib/tar.gz/998e0a84e4c1572ca279ff05007af6ec6639405a --output /work/source.tar.gz
sha256sum /work/source.tar.gz | tee /work/evidence/archive.sha256
tar --extract --gzip --file /work/source.tar.gz --directory /work/source --strip-components=1 --no-same-owner
cd /work/source
sha256sum --check /opt/nanoda/expected.sha256
actual_files=$(find . -type f | wc -l)
expected_files=$(wc -l < /opt/nanoda/expected.sha256)
[ "$actual_files" -eq "$expected_files" ]
[ -z "$(find . -type l -print -quit)" ]
cargo fetch --locked --target x86_64-unknown-linux-gnu
sha256sum --check /opt/nanoda/expected.sha256
