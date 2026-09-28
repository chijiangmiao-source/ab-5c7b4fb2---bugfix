"""HTTP 接口单元测试:健康路径、审计接口、错误码。"""
import json
import threading
import unittest
import urllib.error
import urllib.request
from http.server import ThreadingHTTPServer

from app.server import Handler


class ApiTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        cls.port = cls.server.server_address[1]
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        cls.thread.join(timeout=5)

    def _get(self, path):
        try:
            with urllib.request.urlopen(
                    f"http://127.0.0.1:{self.port}{path}", timeout=5) as resp:
                return resp.status, json.loads(resp.read())
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read())

    def _post(self, path, payload=None, raw=None):
        data = raw if raw is not None else json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            f"http://127.0.0.1:{self.port}{path}", data=data,
            headers={"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=5) as resp:
                return resp.status, json.loads(resp.read())
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read())

    def test_health(self):
        code, body = self._get("/health")
        self.assertEqual(code, 200)
        self.assertEqual(body["status"], "ok")
        self.assertIn("version", body)

    def test_audit_pass(self):
        code, body = self._post("/audit", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 2}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 2}},
                {"id": 1, "op": "halt"},
            ],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "pass")

    def test_audit_fail(self):
        code, body = self._post("/audit", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "add", "reg": 0, "value": 4},
                {"id": 1, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<", "value": 4}},
                {"id": 2, "op": "halt"},
            ],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "fail")
        self.assertEqual(body["first_unproven"]["point"], 1)
        self.assertEqual(body["first_unproven"]["kind"], "abstract_alarm")

    def test_audit_structural_error(self):
        code, body = self._post("/audit", {
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [{"id": 0, "op": "goto", "target": 0}],
        })
        self.assertEqual(code, 200)
        self.assertEqual(body["verdict"], "error")
        self.assertNotIn("points", body)

    def test_bad_json(self):
        code, body = self._post("/audit", raw=b"{not json")
        self.assertEqual(code, 400)

    def test_not_found(self):
        code, _ = self._get("/nope")
        self.assertEqual(code, 404)
        code, _ = self._post("/health", {})
        self.assertEqual(code, 404)


if __name__ == "__main__":
    unittest.main()
