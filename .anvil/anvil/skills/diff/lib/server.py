"""Localhost server wrapper for `anvil:diff` (issue #925).

Ephemeral, read-only, localhost-only: binds ``127.0.0.1`` on an
OS-assigned port, serves ONE pre-rendered HTML page for every request,
prints the URL, and serves until interrupted. Never re-opens or re-reads
any input path -- the HTML is rendered once (by
``anvil.lib.prose_diff.render_html``) *before* this module is invoked,
and every request handler here only ever serves the same in-memory
bytes. No daemon, no state directory, no auth (constraint per the issue:
this is a trusted-operator local tool, not a network service).
"""

from __future__ import annotations

import http.server
from typing import Callable

__all__ = [
    "ALLOWED_HOST",
    "build_server",
    "url_for",
    "serve_until_interrupt",
]


# Hard constraint (issue #925): "Bind 127.0.0.1 on an ephemeral port ...
# no network exposure." This is the ONLY host `build_server` accepts --
# not `0.0.0.0`, not a LAN IP, not `localhost` (which can resolve to
# `::1` and require a different socket family than stdlib
# `http.server.HTTPServer`'s default `AF_INET`). Keeping the guard to a
# single literal keeps the loopback-only contract easy to eyeball and
# easy to test.
ALLOWED_HOST = "127.0.0.1"


class _DiffPageHandler(http.server.BaseHTTPRequestHandler):
    """Serves the same in-memory HTML for every ``GET`` request.

    A single-page read-only viewer has nothing else to route: there is
    no API, no static-asset directory, no filesystem access at
    request-handling time at all.
    """

    html_bytes: bytes = b""

    def do_GET(self) -> None:  # noqa: N802 - stdlib handler method name
        body = self.html_bytes
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, format: str, *args: object) -> None:  # noqa: A002
        # Quiet by default. The CLI already prints the one URL that
        # matters; a per-request access log is noise for a one-page
        # local viewer intended to be opened once in a browser tab.
        pass


def build_server(html: str, *, port: int = 0) -> http.server.HTTPServer:
    """Build (but do not start serving) the localhost diff-page server.

    Always binds :data:`ALLOWED_HOST` (``127.0.0.1``). ``port=0`` (the
    default) asks the OS for a free ephemeral port; after construction
    the real assigned port is available at ``server.server_address[1]``
    (stdlib ``TCPServer`` binds and starts listening during
    ``__init__`` when ``bind_and_activate`` is left at its default
    ``True``).

    Returns the constructed server so the caller decides how to run it:
    :func:`serve_until_interrupt` (the CLI path) or a single test
    request followed by ``server.server_close()`` (the test path).
    """

    bound_handler = type(
        "_BoundDiffPageHandler",
        (_DiffPageHandler,),
        {"html_bytes": html.encode("utf-8")},
    )
    return http.server.HTTPServer((ALLOWED_HOST, port), bound_handler)


def url_for(server: http.server.HTTPServer) -> str:
    """The one URL this server serves, e.g. ``http://127.0.0.1:54321/``."""

    return f"http://{server.server_address[0]}:{server.server_address[1]}/"


def serve_until_interrupt(
    server: http.server.HTTPServer, *, print_fn: Callable[[str], object] = print
) -> None:
    """Serve ``server`` until ``Ctrl+C``, then close it cleanly.

    ``print_fn`` is injectable so callers (and tests) can capture the
    printed URL instead of writing to real stdout.
    """

    print_fn(f"anvil:diff serving at {url_for(server)} (Ctrl+C to stop)")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
