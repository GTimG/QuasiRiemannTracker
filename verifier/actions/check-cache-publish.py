"""Fail fast when the Build cache workflow could not publish its result.

Runs before any submission is prepared or compiled, so a missing secret, a
wrong key, a token without release access or a proxy that refuses uploads is
reported in seconds instead of after a long build. No submitted code has run
when this step receives the key.
"""
from pathlib import Path
import json, os, subprocess, sys, tempfile, urllib.error, urllib.request
sys.path.insert(0, str(Path(__file__).resolve().parent))
from cache_release import KEY, REPOSITORY, TAG


def check_key(pem):
    if not pem.strip():
        return 'The QRH_BUILD_CACHE_KEY secret of the build-cache environment is missing or empty'
    with tempfile.TemporaryDirectory() as tmp:
        key = Path(tmp)/'signing-key.pem'
        key.touch(mode=0o600)
        key.write_text(pem)
        derived = subprocess.run(['openssl', 'pkey', '-in', str(key), '-pubout'],
                                 capture_output=True, text=True)
    if derived.returncode:
        return 'QRH_BUILD_CACHE_KEY is not a readable private key'
    if derived.stdout.strip() != KEY.read_text().strip():
        return 'QRH_BUILD_CACHE_KEY does not match verifier/standard/build-cache-public.pem'
    return None


def check_release(token):
    request = urllib.request.Request(f'https://api.github.com/repos/{REPOSITORY}/releases/tags/{TAG}',
        headers={'Authorization': 'Bearer '+token, 'Accept': 'application/vnd.github+json'})
    try:
        urllib.request.urlopen(request, timeout=30).close()
    except urllib.error.HTTPError as error:
        # A missing release is created on first publication.
        if error.code != 404:
            return f'The job token cannot read the {TAG} release (HTTP {error.code})'
    except urllib.error.URLError as error:
        return f'api.github.com is unreachable: {error.reason}'
    return None


def check_upload_route():
    # Any HTTP answer proves the proxy tunnels to the upload host; a refused
    # CONNECT surfaces as a URLError instead.
    try:
        urllib.request.urlopen('https://uploads.github.com/', timeout=30).close()
    except urllib.error.HTTPError:
        pass
    except urllib.error.URLError as error:
        return f'uploads.github.com is unreachable through the runner proxy: {error.reason}'
    return None


def main():
    pem, token = os.environ.pop('QRH_BUILD_CACHE_KEY', ''), os.environ.pop('GH_TOKEN', '')
    problems = [p for p in [check_key(pem),
                            check_release(token) if token else 'The job token is missing',
                            check_upload_route()] if p]
    for problem in problems:
        print(f'::error::{problem}', flush=True)
    if problems:
        raise SystemExit(1)
    print('Signing key, release access and upload route are ready', flush=True)


if __name__ == '__main__':
    main()
