FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ARG RUNNER_VERSION=2.338.2
ARG RUNNER_SHA256=baebf204307bac6193480852732f0aba2ae97b6c5597c244f4d5558390147c40
ARG NODE_VERSION=22.22.1
ARG NODE_SHA256=9a6bc82f9b491279147219f6a18add1e18424dce90d41d2a5fcd69d4924ba3aa
ARG CLOUD_IMAGE_DATE=20261017
ARG CLOUD_IMAGE_SHA256=04e8f2461a16a44e78a370284471f29616cdd9baf1893df25807b71f985b6c94

ENV DEBIAN_FRONTEND=noninteractive \
    LANG=C.UTF-8 \
    HOME=/runner/home \
    PATH=/opt/node/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1

# The outer process needs only KVM. Guest sudo, AppArmor and cgroups belong to
# the disposable guest kernel; the host container remains unprivileged.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       ca-certificates cloud-image-utils curl genisoimage git jq \
       libicu74 liblttng-ust1t64 libssl3t64 libunwind8 \
       python3 qemu-system-x86 qemu-utils seabios socat tar \
       unzip util-linux xz-utils zlib1g \
    && rm -rf /var/lib/apt/lists/* \
    && mkdir -p /opt/node /opt/runner /opt/payload /runner /vm \
    && groupadd --gid 10001 runner \
    && useradd --uid 10001 --gid 10001 --home-dir /runner/home --no-create-home --shell /bin/bash runner \
    && chown 10001:10001 /vm \
    && chmod 0700 /vm

RUN curl --fail --silent --show-error --location --retry 3 --proto '=https' --tlsv1.2 \
      "https://nodejs.org/dist/v${NODE_VERSION}/node-v${NODE_VERSION}-linux-x64.tar.xz" \
      --output /opt/payload/node.tar.xz \
    && echo "${NODE_SHA256}  /opt/payload/node.tar.xz" | sha256sum --check --strict \
    && tar --extract --xz --file /opt/payload/node.tar.xz --strip-components=1 --directory /opt/node \
    && curl --fail --silent --show-error --location --retry 3 --proto '=https' --tlsv1.2 \
      "https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz" \
      --output /opt/payload/runner.tar.gz \
    && echo "${RUNNER_SHA256}  /opt/payload/runner.tar.gz" | sha256sum --check --strict \
    && tar --extract --gzip --file /opt/payload/runner.tar.gz --directory /opt/runner \
    && chmod -R a+rX /opt/node /opt/runner /opt/payload

RUN curl --fail --silent --show-error --location --retry 3 --proto '=https' --tlsv1.2 \
      "https://cloud-images.ubuntu.com/noble/${CLOUD_IMAGE_DATE}/noble-server-cloudimg-amd64.img" \
      --output /opt/guest-base.qcow2 \
    && echo "${CLOUD_IMAGE_SHA256}  /opt/guest-base.qcow2" | sha256sum --check --strict \
    && chmod 0444 /opt/guest-base.qcow2

COPY --chmod=0555 guest.sh /opt/payload/guest.sh
RUN genisoimage -quiet -output /opt/tools.iso -volid QRH_TOOLS -R -J /opt/payload \
    && chmod 0444 /opt/tools.iso
COPY --chmod=0444 vm.py /opt/runner-vm.py
COPY --chmod=0555 entrypoint.sh /usr/local/bin/runner-entrypoint

USER 10001:10001
WORKDIR /runner
# Apply NNP after Docker enters AppArmor: snap Docker cannot do that profile
# transition when Docker sets NNP before exec (LP#1908448).
ENTRYPOINT ["/usr/bin/setpriv", "--no-new-privs", "/usr/local/bin/runner-entrypoint"]
