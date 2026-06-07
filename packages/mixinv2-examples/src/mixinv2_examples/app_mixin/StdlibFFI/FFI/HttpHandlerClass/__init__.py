"""A BaseHTTPRequestHandler subclass that dispatches GET to Request.response.

The handler class is defined at module level; the Request scope factory is injected
via a class variable by the ``handlerClass`` resource.
"""

from http.server import BaseHTTPRequestHandler
from typing import ClassVar, Protocol

from mixinv2 import public, resource


class _RequestScopeInstance(Protocol):
    response: object


class _RequestScopeFactory(Protocol):
    def __call__(self, request: BaseHTTPRequestHandler) -> _RequestScopeInstance: ...


class _Handler(BaseHTTPRequestHandler):
    _request_factory: ClassVar[_RequestScopeFactory]

    def do_GET(self) -> None:
        type(self)._request_factory(request=self).response

    def log_message(self, format: str, *arguments: object) -> None:
        pass


@public
@resource
def handlerClass(Request: _RequestScopeFactory) -> type:
    _Handler._request_factory = Request
    return _Handler
