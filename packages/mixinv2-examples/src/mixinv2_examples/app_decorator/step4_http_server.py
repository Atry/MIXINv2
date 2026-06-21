"""Step 4: app scope vs request scope — full HTTP server with SQLite."""

import sqlite3
from http.server import BaseHTTPRequestHandler, HTTPServer
from typing import Callable, Protocol

from mixinv2 import LexicalReference
from mixinv2 import extend, extern, public, resource, scope


# [docs:step4-http-server]
class _Handler(BaseHTTPRequestHandler):
    def do_GET(self) -> None:
        self.server.request_scope_factory(request=self).responseSent  # type: ignore[attr-defined]

    def log_message(self, format: str, *arguments: object) -> None:
        pass
@scope
class SQLiteDatabase:
    @extern
    def databasePath() -> str: ...    # database owns its own config

    # App-scoped: one connection for the entire process lifetime.
    # check_same_thread=False: created in main thread, used in handler threads.
    @public
    @resource
    def connection(databasePath: str) -> sqlite3.Connection:
        db = sqlite3.connect(databasePath, check_same_thread=False)
        db.execute(
            "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT)"
        )
        db.execute("INSERT INTO users VALUES (1, 'alice')")
        db.execute("INSERT INTO users VALUES (2, 'bob')")
        db.commit()
        return db

@scope
class UserRepository:
    @extern
    def connection() -> sqlite3.Connection: ...

    # @scope as a composable dataclass — fields are @extern, constructed via DI.
    @public
    @scope
    class User:
        @public
        @extern
        def userId() -> int: ...

        @public
        @extern
        def name() -> str: ...

    # App-scoped: total count across all requests.
    @public
    @resource
    def userCount(connection: sqlite3.Connection) -> int:
        (count,) = connection.execute(
            "SELECT COUNT(*) FROM users"
        ).fetchone()
        return count

    # Request-scoped: per-request DB resources, wired by overlay union-mount.
    @public
    @scope
    class Request:
        @extern
        def userId() -> int: ...  # provided by HttpHandlers.Request

        @public
        @resource
        def currentUser(
            connection: sqlite3.Connection, userId: int, User: Callable
        ) -> object:
            row = connection.execute(
                "SELECT id, name FROM users WHERE id = ?", (userId,)
            ).fetchone()
            assert row is not None, f"no user with id={userId}"
            identifier, name = row
            return User(userId=identifier, name=name)

@scope
class HttpHandlers:
    @extern
    def userCount() -> int: ...

    # Request is nested because its lifetime is per-request,
    # not per-application.
    @public
    @scope
    class Request:
        class _RequestWithPath(Protocol):
            path: str

        @extern
        def request() -> BaseHTTPRequestHandler: ...

        @extern
        def currentUser() -> object: ...

        # userId is extracted from the request and injected into
        # UserRepository.Request.currentUser automatically.
        @public
        @resource
        def userId(request: _RequestWithPath) -> int:
            return int(request.path.split("/")[-1])

        @public
        @resource
        def responseBody(userCount: int, currentUser: object) -> bytes:
            return (
                f"total={userCount} current={currentUser.name}"
            ).encode()

        # IO resource: sends the HTTP response as a side effect.
        @public
        @resource
        def responseSent(
            request: BaseHTTPRequestHandler,
            responseBody: bytes,
        ) -> None:
            request.send_response(200)
            request.end_headers()
            request.wfile.write(responseBody)

@scope
class NetworkServer:
    @extern
    def host() -> str: ...             # network layer owns its own config

    @extern
    def port() -> int: ...

    @scope
    class Request:
        pass

    # Request is injected by name as a Callable (StaticScope).
    # Calling Request(request=handler) returns a fresh InstanceScope.
    @public
    @resource
    def server(host: str, port: int, Request: Callable) -> HTTPServer:
        http_server = HTTPServer((host, port), _Handler)
        http_server.request_scope_factory = Request  # type: ignore[attr-defined]
        return http_server

@extend(
    LexicalReference(path=("SQLiteDatabase",)),
    LexicalReference(path=("UserRepository",)),
    LexicalReference(path=("HttpHandlers",)),
    LexicalReference(path=("NetworkServer",)),
)
@public
@scope
class App:
    pass
# [/docs:step4-http-server]
