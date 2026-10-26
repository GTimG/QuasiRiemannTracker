set -euo pipefail
mkdir -p /work/bundle
cd /work/source
sha256sum --check /opt/nanoda/expected.sha256 > /work/bundle/source-before.log
{ date -u +'%Y-%m-%dT%H:%M:%SZ'; rustc -vV; cargo -vV; cc --version; ld --version; ldd --version; uname -a; } > /work/bundle/toolchain-versions.txt 2>&1
cargo test --locked --offline --jobs 4 2>&1 | tee /work/bundle/test.log
cargo build --release --locked --offline --jobs 4 2>&1 | tee /work/bundle/build.log
sha256sum --check /opt/nanoda/expected.sha256 > /work/bundle/source-after.log
cp /work/build/release/nanoda_bin /work/bundle/nanoda_bin
cp Cargo.lock LICENSE /work/bundle/
cp /opt/nanoda/expected-source-manifest.json /work/bundle/source-manifest.json
cp /work/evidence/fetch.log /work/evidence/archive.sha256 /work/bundle/
sha256sum /work/bundle/nanoda_bin
file /work/bundle/nanoda_bin
ldd /work/bundle/nanoda_bin
