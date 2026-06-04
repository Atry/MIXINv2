"""NetworkServer: HTTP server, owns host/port config, no business logic."""

from http.server import BaseHTTPRequestHandler, HTTPServer
from typing import Callable

from mixinv2 import extern, public, resource


class _Handler(BaseHTTPRequestHandler):
    def do_GET(self) -> None:
        self.server.request_scope_factory(request=self).responseSent  # type: ignore[attr-defined]

    def log_message(self, format: str, *arguments: object) -> None:
        pass


@extern
def host() -> str: ...


@extern
def port() -> int: ...


@public
@resource
def server(host: str, port: int, Request: Callable) -> HTTPServer:
    http_server = HTTPServer((host, port), _Handler)
    http_server.request_scope_factory = Request  # type: ignore[attr-defined]
    return http_server


@public
@resource
def serveForever(server: HTTPServer) -> None:
    host, port = server.server_address
    print(f"Serving on http://{host}:{port}")
    server.serve_forever()
