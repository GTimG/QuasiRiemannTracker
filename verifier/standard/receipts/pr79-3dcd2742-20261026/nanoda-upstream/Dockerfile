FROM rust@sha256:b36c246742b4d323472588f789601be34eb4af053255e2af53969078ee8dcec7
RUN mkdir /work && chown 10001:10001 /work
COPY fetch.sh build.sh expected.sha256 expected-source-manifest.json /opt/nanoda/
USER 10001:10001
WORKDIR /work
ENV HOME=/work/home CARGO_HOME=/work/cargo CARGO_TARGET_DIR=/work/build
ENTRYPOINT ["/bin/bash"]
