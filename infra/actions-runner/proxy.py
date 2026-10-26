#!/usr/bin/env python3
"""Bounded HTTPS CONNECT gateway for the isolated Actions runner network.

Only the operator can change this file or PROXY_DENY_CIDRS. The job container
must have no route to the Internet except this proxy, and no route to the host.
This is destination filtering, not TLS inspection or data-loss prevention:
allowed GitHub and Azure services can carry user-controlled content.
"""

import ipaddress
import logging
import os
import re
import selectors
import socket
import socketserver
import threading
import time

PORT = 3128
MAX_CONNECTIONS = 64
MAX_HEADER_BYTES = 16384
HEADER_TIMEOUT = 10
CONNECT_TIMEOUT = 10
IDLE_TIMEOUT = 300
MAX_TUNNEL_SECONDS = 7200
BUFFER_BYTES = 65536

# GitHub's documented runner destinations, plus this repository's tool sources.
# https://docs.github.com/en/actions/reference/runners/self-hosted-runners
EXACT_HOSTS = frozenset(
    {
        "github.com",
        "api.github.com",
        "codeload.github.com",
        "raw.githubusercontent.com",
        "objects.githubusercontent.com",
        "objects-origin.githubusercontent.com",
        "github-releases.githubusercontent.com",
        "github-registry-files.githubusercontent.com",
        "release-assets.githubusercontent.com",
        "registry.npmjs.org",
        "cache.mathlib.org",
        "archive.ubuntu.com",
        "security.ubuntu.com",
        "nodejs.org",
        "cdn.playwright.dev",
        "download.prss.microsoft.com",
        "playwright.download.prss.microsoft.com",
    }
)
WILDCARD_SUFFIXES = (".actions.githubusercontent.com", ".blob.core.windows.net")
HOSTNAME = re.compile(r"(?:[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?\.)*[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?\Z")
HEADER_NAME = re.compile(rb"[!#$%&'*+.^_`|~0-9A-Za-z-]+\Z")

# Explicitly cover special networks whose classification differs between Python
# releases. IPv6 must additionally be ordinary public unicast (2000::/3).
SPECIAL_NETWORKS = tuple(
    ipaddress.ip_network(value)
    for value in (
        "0.0.0.0/8",
        "100.64.0.0/10",
        "192.0.0.0/24",
        "192.88.99.0/24",
        "198.18.0.0/15",
        "2001::/23",
        "2002::/16",
    )
)
PUBLIC_IPV6 = ipaddress.ip_network("2000::/3")


class Rejected(ValueError):
    """A request is outside the gateway policy."""


def allowed_host(host):
    return (
        len(host) <= 253
        and HOSTNAME.fullmatch(host) is not None
        and (host in EXACT_HOSTS or any(host.endswith(suffix) for suffix in WILDCARD_SUFFIXES))
    )


def parse_target(authority):
    # IP literals, user-info, escaping, paths, and alternative ports never match.
    host, separator, port = authority.rpartition(":")
    host = host.lower()
    if separator != ":" or port != "443" or not allowed_host(host):
        raise Rejected("destination denied")
    return host


def parse_request(header):
    if len(header) > MAX_HEADER_BYTES or not header.endswith(b"\r\n\r\n"):
        raise Rejected("invalid headers")
    lines = header[:-4].split(b"\r\n")
    try:
        method, authority, version = lines[0].decode("ascii").split(" ")
    except (UnicodeDecodeError, ValueError) as error:
        raise Rejected("invalid request") from error
    if method != "CONNECT" or version not in ("HTTP/1.0", "HTTP/1.1"):
        raise Rejected("CONNECT required")
    host = parse_target(authority)
    seen = set()
    for line in lines[1:]:
        name, separator, value = line.partition(b":")
        if not separator or not HEADER_NAME.fullmatch(name):
            raise Rejected("invalid header")
        if any(byte < 32 and byte != 9 or byte > 126 for byte in value):
            raise Rejected("invalid header value")
        name = name.lower()
        value = value.strip()
        if name in seen:
            raise Rejected("duplicate header")
        seen.add(name)
        if name == b"transfer-encoding" or (name == b"content-length" and value != b"0"):
            raise Rejected("CONNECT cannot carry an HTTP body")
        # Undici omits the default HTTPS port in Host for a CONNECT authority
        # that includes :443. Both spellings identify the same checked target.
        if name == b"host" and value.lower() not in (host.encode("ascii"), (host + ":443").encode("ascii")):
            raise Rejected("conflicting host header")
    return host


def parse_deny_networks(value):
    # Invalid operator configuration fails startup rather than weakening policy.
    return tuple(ipaddress.ip_network(part.strip(), strict=False) for part in value.split(",") if part.strip())


def public_address(value, deny_networks=()):
    if "%" in value:
        return False
    try:
        address = ipaddress.ip_address(value)
    except ValueError:
        return False
    if not address.is_global or address.is_multicast or address.is_reserved:
        return False
    if address.version == 6 and (address.ipv4_mapped is not None or address not in PUBLIC_IPV6):
        return False
    return not any(address in network for network in (*SPECIAL_NETWORKS, *deny_networks))


def resolve_public(host, deny_networks=()):
    # Resolve once, validate the entire answer, and connect to a numeric sockaddr.
    # Never hand the hostname to connect(), which could perform a second lookup.
    answers = socket.getaddrinfo(host, 443, type=socket.SOCK_STREAM, proto=socket.IPPROTO_TCP)
    if not answers:
        raise Rejected("empty DNS answer")
    endpoints = []
    for family, kind, protocol, _canonical, address in answers:
        if family not in (socket.AF_INET, socket.AF_INET6) or not public_address(address[0], deny_networks):
            raise Rejected("non-public DNS answer")
        if address[1] != 443 or (family == socket.AF_INET6 and address[3] != 0):
            raise Rejected("invalid DNS endpoint")
        endpoint = (family, kind, protocol, address)
        if endpoint not in endpoints:
            endpoints.append(endpoint)
    return endpoints


def connect_public(host, deny_networks=()):
    endpoints = resolve_public(host, deny_networks)
    deadline = time.monotonic() + CONNECT_TIMEOUT
    last_error = None
    for family, kind, protocol, address in endpoints:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        upstream = socket.socket(family, kind, protocol)
        try:
            upstream.settimeout(min(remaining, 3))
            upstream.connect(address)
            return upstream
        except OSError as error:
            last_error = error
            upstream.close()
    raise OSError("upstream unavailable") from last_error


def read_header(client):
    deadline = time.monotonic() + HEADER_TIMEOUT
    data = bytearray()
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise Rejected("header timeout")
        client.settimeout(remaining)
        block = client.recv(min(4096, MAX_HEADER_BYTES - len(data)))
        if not block:
            raise Rejected("incomplete headers")
        data.extend(block)
        end = data.find(b"\r\n\r\n")
        if end >= 0:
            return bytes(data[: end + 4]), bytes(data[end + 4 :])
        if len(data) >= MAX_HEADER_BYTES:
            raise Rejected("headers too large")


def relay(client, upstream, initial=b""):
    peers = {client: upstream, upstream: client}
    pending = {client: bytearray(), upstream: bytearray(initial)}
    readers = set(peers)
    finished_writes = set()
    started = last_activity = time.monotonic()
    for stream in peers:
        stream.setblocking(False)
    with selectors.DefaultSelector() as selector:
        while readers or any(pending.values()):
            now = time.monotonic()
            timeout = min(IDLE_TIMEOUT - (now - last_activity), MAX_TUNNEL_SECONDS - (now - started))
            if timeout <= 0:
                return
            for stream, peer in peers.items():
                events = 0
                if stream in readers and len(pending[peer]) < BUFFER_BYTES:
                    events |= selectors.EVENT_READ
                if pending[stream]:
                    events |= selectors.EVENT_WRITE
                elif peer not in readers and stream not in finished_writes:
                    stream.shutdown(socket.SHUT_WR)
                    finished_writes.add(stream)
                try:
                    selector.unregister(stream)
                except KeyError:
                    pass
                if events:
                    selector.register(stream, events)
            for key, events in selector.select(timeout):
                stream = key.fileobj
                peer = peers[stream]
                if events & selectors.EVENT_READ:
                    try:
                        block = stream.recv(BUFFER_BYTES - len(pending[peer]))
                    except BlockingIOError:
                        continue
                    if block:
                        pending[peer].extend(block)
                        last_activity = time.monotonic()
                    else:
                        readers.discard(stream)
                if events & selectors.EVENT_WRITE:
                    try:
                        sent = stream.send(pending[stream])
                    except BlockingIOError:
                        continue
                    if sent:
                        del pending[stream][:sent]
                        last_activity = time.monotonic()


class ProxyHandler(socketserver.BaseRequestHandler):
    def handle(self):
        tunnel_started = False
        try:
            header, initial = read_header(self.request)
            host = parse_request(header)
            with connect_public(host, self.server.deny_networks) as upstream:
                self.request.settimeout(CONNECT_TIMEOUT)
                self.request.sendall(b"HTTP/1.1 200 Connection Established\r\n\r\n")
                tunnel_started = True
                relay(self.request, upstream, initial)
        except Rejected as error:
            logging.info("request rejected: %s", error)
            self.reject(403)
        except (OSError, ValueError):
            if not tunnel_started:
                self.reject(502)

    def reject(self, status):
        try:
            self.request.settimeout(1)
            self.request.sendall(f"HTTP/1.1 {status} Rejected\r\nConnection: close\r\nContent-Length: 0\r\n\r\n".encode("ascii"))
        except OSError:
            pass


class ProxyServer(socketserver.ThreadingMixIn, socketserver.TCPServer):
    allow_reuse_address = True
    daemon_threads = True
    request_queue_size = MAX_CONNECTIONS

    def __init__(self, address, deny_networks=()):
        self.deny_networks = deny_networks
        self.slots = threading.BoundedSemaphore(MAX_CONNECTIONS)
        super().__init__(address, ProxyHandler)

    def process_request(self, request, address):
        if not self.slots.acquire(blocking=False):
            self.shutdown_request(request)
            return
        try:
            super().process_request(request, address)
        except BaseException:
            self.slots.release()
            raise

    def process_request_thread(self, request, address):
        try:
            super().process_request_thread(request, address)
        finally:
            self.slots.release()


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
    deny_networks = parse_deny_networks(os.environ.get("PROXY_DENY_CIDRS", ""))
    with ProxyServer(("0.0.0.0", PORT), deny_networks) as server:
        logging.info("HTTPS destination gateway listening on port %s", PORT)
        server.serve_forever(poll_interval=0.5)
