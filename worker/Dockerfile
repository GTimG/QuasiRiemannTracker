# Online construction uses only maintainer-controlled files. No submission enters this build.
FROM rust:1.90.0-bookworm@sha256:3914072ca0c3b8aad871db9169a651ccfce30cf58303e5d6f2db16d1d8a7e58f AS nanoda
RUN git clone https://github.com/ammkrn/nanoda_lib.git /src && cd /src && git checkout --detach 3a2407216ee84a75f9e1aead6803d0578be06ae7 && cargo build --release --locked
FROM golang:1.25.2-bookworm@sha256:42d8e9dea06f23d0bfc908826455213ee7f3ed48c43e287a422064220c501be9 AS landrun
RUN git clone https://github.com/Zouuup/landrun.git /src && cd /src && git checkout --detach 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4 && CGO_ENABLED=1 go build -mod=readonly -o /landrun ./cmd/landrun
FROM ubuntu:24.04@sha256:534baea6a22c03a63003dbc8dbe78fe34bc0d7e595d9a9dc9834884ff530eb55 AS build
ARG TARGETARCH
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git zstd python3 build-essential libgmp-dev && rm -rf /var/lib/apt/lists/*
RUN case "$TARGETARCH" in amd64) QRH_ARCH=linux;; arm64) QRH_ARCH=linux_aarch64;; *) exit 1;; esac && curl -fL --retry 3 "https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-${QRH_ARCH}.tar.zst" -o /tmp/lean.tar.zst && mkdir /opt/lean && tar --zstd -xf /tmp/lean.tar.zst -C /opt/lean --strip-components=1 && rm /tmp/lean.tar.zst
ENV PATH="/opt/lean/bin:/opt/bin:/usr/bin:/bin"
RUN git clone https://github.com/leanprover/comparator.git /opt/comparator && cd /opt/comparator && git checkout --detach d03acab154d269c06e60e4de7e4cc85deebff94b && printf 'leanprover/lean4:v4.34.1\n' > lean-toolchain && mkdir -p .lake/packages && git clone https://github.com/leanprover/lean4export.git .lake/packages/lean4export && cd .lake/packages/lean4export && git checkout --detach 076e8e57707e813375e8f9da8bf989799ace9680 && printf 'leanprover/lean4:v4.34.1\n' > lean-toolchain
RUN cd /opt/comparator && lake build comparator lean4export && mkdir /opt/bin && cp .lake/build/bin/comparator .lake/packages/lean4export/.lake/build/bin/lean4export /opt/bin/
COPY --from=nanoda /src/target/release/nanoda_bin /opt/bin/
COPY --from=landrun /landrun /opt/bin/
COPY worker /opt/qrh/worker
COPY verifier/pins.json verifier/upstream-challenge.lean /opt/qrh/verifier/
RUN python3 /opt/qrh/worker/bootstrap.py
RUN chmod -R a+rX /opt && mkdir -p /work && chmod 1777 /work
# The image is immutable and is pinned by its inspected sha256 ID, never by this build tag.
USER 65532:65532
WORKDIR /work
ENTRYPOINT ["/usr/bin/python3","/opt/qrh/worker/entrypoint.py"]
