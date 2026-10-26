#!/usr/bin/env bash
set -euo pipefail
umask 077

if [[ "$(id -u)" != 10001 ]]; then
  echo "Runner must execute as the unprivileged runner user." >&2
  exit 1
fi

if [[ "${1:-}" == "--register" && "$#" == 1 ]]; then
  # Only the registration container consumes the short-lived token. The VM
  # receives the resulting single-job identity, never this registration token.
  cp -a /opt/runner/bin /runner/bin
  ln -s /opt/runner/externals /runner/externals
  mkdir -p "$HOME" /runner/_work
  printf '%s\n' "$PATH" > /runner/.path
  : > /runner/.env
  IFS= read -r registration_token || [[ -n "${registration_token:-}" ]]
  if [[ ! "$registration_token" =~ ^[A-Za-z0-9_]{20,128}$ ]]; then
    echo "Invalid runner registration token format." >&2
    exit 1
  fi
  runner_name="${QRH_RUNNER_NAME:-Zoo-MM-QuasiRiemannTracker-proof-${HOSTNAME}}"
  if [[ ! "$runner_name" =~ ^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$ ]]; then
    echo "Invalid runner name format." >&2
    exit 1
  fi
  /runner/bin/Runner.Listener configure \
    --unattended \
    --url https://github.com/GTimG/QuasiRiemannTracker \
    --token "$registration_token" \
    --name "$runner_name" \
    --labels qrh-proof \
    --work _work \
    --ephemeral \
    --disableupdate >&2
  unset registration_token
  python3 -c 'import json; assert json.load(open("/runner/.runner", encoding="utf-8-sig")).get("ephemeral") is True, "Registration must be ephemeral"'
  exec tar --create --file=- --directory=/runner -- .runner .credentials .credentials_rsaparams
fi

if [[ "$#" == 0 ]]; then
  exec python3 /opt/runner-vm.py
fi
if [[ "$#" == 1 && "$1" == "--smoke" ]]; then
  exec python3 /opt/runner-vm.py --smoke
fi

echo "Usage: runner-entrypoint [--register|--smoke]" >&2
exit 1
