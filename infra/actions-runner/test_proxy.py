"""Policy and socket tests; no network access to GitHub is required."""

import socket
import threading
import unittest
from unittest.mock import Mock, patch

import proxy


class DestinationPolicyTests(unittest.TestCase):
    def test_expected_ci_hosts(self):
        for host in (
            "github.com", "api.github.com", "codeload.github.com",
            "release-assets.githubusercontent.com", "raw.githubusercontent.com",
            "pipelines.actions.githubusercontent.com",
            "productionresultssa0.blob.core.windows.net",
            "registry.npmjs.org", "cache.mathlib.org", "nodejs.org", "cdn.playwright.dev",
            "download.prss.microsoft.com", "playwright.download.prss.microsoft.com",
        ):
            with self.subTest(host=host):
                self.assertEqual(proxy.parse_target(host + ":443"), host)

    def test_alternative_authorities_cannot_bypass_allowlist(self):
        for authority in (
            "127.0.0.1:443", "10.0.0.1:443", "169.254.169.254:443",
            "[::1]:443", "2130706433:443", "github.com:80", "github.com:0443",
            "github.com", "github.com.:443", "github.com@evil.test:443",
            "evil.test@github.com:443", "github.com.evil.test:443",
            "evil.cache.mathlib.org:443", "cache.mathlib.org.evil.test:443",
            "evil-actions.githubusercontent.com:443", "actions.githubusercontent.com.evil.test:443",
            "evilblob.core.windows.net:443", "github.com/path:443",
            "github.com%00.evil.test:443", "github.com\\evil:443",
            "github.com\n:443", "evil.test:443", "-foo.actions.githubusercontent.com:443",
            "a..actions.githubusercontent.com:443", "аpi.github.com:443",
        ):
            with self.subTest(authority=authority):
                with self.assertRaises(proxy.Rejected):
                    proxy.parse_target(authority)

    def test_public_internet_addresses(self):
        self.assertTrue(proxy.public_address("140.82.112.4"))
        self.assertTrue(proxy.public_address("2606:4700:4700::1111"))

    def test_special_ip_networks_are_denied(self):
        for address in (
            "0.0.0.0", "10.1.2.3", "127.0.0.1", "100.64.1.2",
            "169.254.169.254", "172.17.0.1", "192.168.1.1", "192.0.0.9",
            "192.88.99.1", "192.0.2.1", "198.18.0.1", "198.51.100.1",
            "203.0.113.1", "224.0.0.1", "240.0.0.1", "255.255.255.255",
            "::", "::1", "::ffff:127.0.0.1", "::ffff:140.82.112.4",
            "64:ff9b::a00:1", "64:ff9b:1::a00:1", "2001:db8::1",
            "2001::a00:1", "2002:0a00:0001::1", "fc00::1", "fe80::1",
            "ff02::1", "2606:4700:4700::1111%eth0", "not-an-address",
        ):
            with self.subTest(address=address):
                self.assertFalse(proxy.public_address(address))

    def test_operator_can_block_host_public_ip_and_network(self):
        denied = proxy.parse_deny_networks("140.82.112.4, 2606:4700:4700::/48")
        self.assertFalse(proxy.public_address("140.82.112.4", denied))
        self.assertFalse(proxy.public_address("2606:4700:4700::1111", denied))
        self.assertTrue(proxy.public_address("140.82.112.5", denied))
        with self.assertRaises(ValueError):
            proxy.parse_deny_networks("not-an-address")

    def test_mixed_public_private_dns_answer_is_rejected(self):
        answers = [
            (socket.AF_INET, socket.SOCK_STREAM, socket.IPPROTO_TCP, "", ("140.82.112.4", 443)),
            (socket.AF_INET, socket.SOCK_STREAM, socket.IPPROTO_TCP, "", ("127.0.0.1", 443)),
        ]
        with patch.object(proxy.socket, "getaddrinfo", return_value=answers):
            with self.assertRaises(proxy.Rejected):
                proxy.resolve_public("github.com")

    def test_dns_is_resolved_once_and_numeric_address_is_connected(self):
        answer = (socket.AF_INET, socket.SOCK_STREAM, socket.IPPROTO_TCP, "", ("140.82.112.4", 443))
        upstream = Mock()
        with patch.object(proxy.socket, "getaddrinfo", side_effect=[[answer], AssertionError("DNS rebound")]) as resolve:
            with patch.object(proxy.socket, "socket", return_value=upstream):
                self.assertIs(proxy.connect_public("github.com"), upstream)
        resolve.assert_called_once()
        upstream.connect.assert_called_once_with(("140.82.112.4", 443))


class RequestTests(unittest.TestCase):
    def test_standard_connect(self):
        header = b"CONNECT GitHub.com:443 HTTP/1.1\r\nHost: github.com:443\r\nProxy-Connection: Keep-Alive\r\n\r\n"
        self.assertEqual(proxy.parse_request(header), "github.com")

    def test_undici_connect_can_omit_default_port_from_host_header(self):
        header = b"CONNECT api.github.com:443 HTTP/1.1\r\nhost: api.github.com\r\nconnection: close\r\n\r\n"
        self.assertEqual(proxy.parse_request(header), "api.github.com")

    def test_unsupported_methods_and_ambiguous_headers(self):
        for header in (
            b"GET https://github.com/ HTTP/1.1\r\n\r\n",
            b"CONNECT github.com:443 HTTP/2.0\r\n\r\n",
            b"CONNECT  github.com:443 HTTP/1.1\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\n\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nHost: evil.test:443\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nHost: github.com:80\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nHost: github.com.evil.test\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nHost: github.com:443\r\nHost: github.com:443\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nContent-Length: 1\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\n Bad: folded\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nBad: hidden\x00value\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nBad: bare\nnewline\r\n\r\n",
            b"CONNECT github.com:443 HTTP/1.1\r\nX: " + b"x" * proxy.MAX_HEADER_BYTES + b"\r\n\r\n",
        ):
            with self.subTest(header=header[:100]):
                with self.assertRaises(proxy.Rejected):
                    proxy.parse_request(header)

    def test_header_reader_preserves_pipelined_tunnel_bytes(self):
        client, server = socket.socketpair()
        self.addCleanup(client.close)
        self.addCleanup(server.close)
        header = b"CONNECT github.com:443 HTTP/1.1\r\n\r\n"
        client.sendall(header + b"tls bytes")
        self.assertEqual(proxy.read_header(server), (header, b"tls bytes"))

    def test_header_reader_rejects_unbounded_request(self):
        client = Mock()
        client.recv.side_effect = lambda amount: b"x" * amount
        with self.assertRaises(proxy.Rejected):
            proxy.read_header(client)
        self.assertEqual(client.recv.call_count, proxy.MAX_HEADER_BYTES // 4096)

    def test_invalid_request_is_rejected_before_dns_or_connect(self):
        with proxy.ProxyServer(("127.0.0.1", 0)) as server:
            thread = threading.Thread(target=server.handle_request)
            with patch.object(proxy, "connect_public") as connect:
                thread.start()
                with socket.create_connection(server.server_address, timeout=2) as client:
                    client.sendall(b"CONNECT 169.254.169.254:443 HTTP/1.1\r\n\r\n")
                    self.assertTrue(client.recv(1024).startswith(b"HTTP/1.1 403 "))
                thread.join(timeout=2)
                connect.assert_not_called()

    def test_tunnel_relays_in_both_directions_and_handles_half_close(self):
        client, proxy_client = socket.socketpair()
        proxy_upstream, upstream = socket.socketpair()
        for stream in (client, proxy_client, proxy_upstream, upstream):
            self.addCleanup(stream.close)
            stream.settimeout(2)
        thread = threading.Thread(target=proxy.relay, args=(proxy_client, proxy_upstream, b"first"), daemon=True)
        thread.start()
        self.assertEqual(upstream.recv(5), b"first")
        client.sendall(b"hello")
        self.assertEqual(upstream.recv(5), b"hello")
        client.shutdown(socket.SHUT_WR)
        self.assertEqual(upstream.recv(1), b"")
        upstream.sendall(b"world")
        self.assertEqual(client.recv(5), b"world")
        upstream.shutdown(socket.SHUT_WR)
        thread.join(timeout=2)
        self.assertFalse(thread.is_alive())


if __name__ == "__main__":
    unittest.main()
