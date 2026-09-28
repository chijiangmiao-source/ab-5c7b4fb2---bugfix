"""HTTP 服务:健康路径(GET /health)与审计接口(POST /audit)。

端口由环境变量 PORT 配置(默认 8080)。服务完全无状态:
每次审计独立计算,结构错误响应不携带任何既往分析证据。
"""
from __future__ import annotations

import json
import os
import sys
import traceback
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlsplit

from . import __version__
from .analyzer import analyze

MAX_BODY = 1 << 20  # 1 MiB
SERVICE_NAME = "octagon-auditor"


def _version() -> str:
    return os.environ.get("APP_VERSION", __version__)


class Handler(BaseHTTPRequestHandler):
    server_version = f"{SERVICE_NAME}/{__version__}"
    protocol_version = "HTTP/1.1"

    def _json(self, code: int, obj) -> None:
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:
        path = urlsplit(self.path).path
        if path == "/health":
            self._json(200, {"status": "ok", "service": SERVICE_NAME, "version": _version()})
        elif path == "/":
            self._json(200, {
                "service": SERVICE_NAME,
                "version": _version(),
                "endpoints": {
                    "GET /health": "健康检查",
                    "POST /audit": "提交保护脚本(num_registers/initial/instructions),返回审计结论",
                },
            })
        else:
            self._json(404, {"error": "not_found", "path": path})

    def do_POST(self) -> None:
        path = urlsplit(self.path).path
        if path != "/audit":
            self._json(404, {"error": "not_found", "path": path})
            return
        try:
            length = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            length = 0
        if length <= 0 or length > MAX_BODY:
            self._json(400, {"error": "bad_request", "detail": "missing or oversized body"})
            return
        raw = self.rfile.read(length)
        try:
            payload = json.loads(raw)
        except (ValueError, UnicodeDecodeError):
            self._json(400, {"error": "bad_request", "detail": "body is not valid JSON"})
            return
        if not isinstance(payload, dict):
            self._json(400, {"error": "bad_request", "detail": "top level must be a JSON object"})
            return
        try:
            result = analyze(payload)
        except Exception:  # 防御:内部异常不泄漏堆栈,也绝不放行
            traceback.print_exc()
            self._json(500, {"verdict": "error", "reason": "internal_error"})
            return
        self._json(200, result)


def main() -> None:
    port = int(os.environ.get("PORT", "8080"))
    server = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    print(f"{SERVICE_NAME} {_version()} listening on :{port}", file=sys.stderr)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
