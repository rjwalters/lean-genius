"""Tests for `anvil:diff`'s localhost server wrapper (issue #925).

Server smoke test per the acceptance criteria: bind an ephemeral port on
127.0.0.1, fetch the page, assert 200 -- and the read-only invariant
(nothing under this module ever touches a filesystem path at all, since
the HTML it serves is a plain in-memory string).

Test filename is distinct per the #58 packaging convention.
"""

from __future__ import annotations

import threading
import urllib.request

from _diff_skill_lib import server


def test_build_server_binds_loopback_and_ephemeral_port() -> None:
    httpd = server.build_server("<html>hi</html>")
    try:
        host, port = httpd.server_address[0], httpd.server_address[1]
        assert host == "127.0.0.1"
        assert port != 0  # OS assigned a real ephemeral port
    finally:
        httpd.server_close()


def test_serve_and_fetch_returns_200_and_body() -> None:
    page = "<!DOCTYPE html><html><body>hello diff</body></html>"
    httpd = server.build_server(page)
    url = server.url_for(httpd)

    thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    thread.start()
    try:
        with urllib.request.urlopen(url, timeout=5) as resp:
            assert resp.status == 200
            body = resp.read().decode("utf-8")
            assert body == page
            assert resp.headers.get("Content-Type", "").startswith("text/html")
    finally:
        httpd.shutdown()
        thread.join(timeout=5)
        httpd.server_close()


def test_url_for_format() -> None:
    httpd = server.build_server("x")
    try:
        url = server.url_for(httpd)
        assert url.startswith("http://127.0.0.1:")
        assert url.endswith("/")
    finally:
        httpd.server_close()


def test_serve_until_interrupt_prints_url_and_closes_on_keyboard_interrupt() -> None:
    printed = []

    class _FakeServer:
        server_address = ("127.0.0.1", 54321)
        closed = False

        def serve_forever(self) -> None:
            raise KeyboardInterrupt

        def server_close(self) -> None:
            self.closed = True

    fake = _FakeServer()
    server.serve_until_interrupt(fake, print_fn=printed.append)

    assert fake.closed is True
    assert len(printed) == 1
    assert "127.0.0.1:54321" in printed[0]
