#!/usr/bin/env python3
"""verify 容器的 HTTP 冒烟:健康路径、审计接口三类结论、镜像构建(版本)核对。

通过环境变量配置:
    APP_URL          被测服务地址(默认 http://127.0.0.1:8080)
    EXPECTED_VERSION 期望的构建版本(默认 1.0.0),与 /health 返回比对

全部检查通过以状态码 0 退出,否则状态码 1。
"""
import json
import os
import sys
import time
import urllib.error
import urllib.request

APP_URL = os.environ.get("APP_URL", "http://127.0.0.1:8080").rstrip("/")
EXPECTED_VERSION = os.environ.get("EXPECTED_VERSION", "1.0.0")
WAIT_SECONDS = float(os.environ.get("SMOKE_WAIT_SECONDS", "30"))

# 含循环与寄存器间关系的脚本: widening + 下降复算后应放行
PASS_CASE = {
    "num_registers": 2,
    "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
    "instructions": [
        {"id": 0, "op": "set", "reg": 0, "value": 0},
        {"id": 1, "op": "set", "reg": 1, "value": 0},
        {"id": 2, "op": "branch",
         "cond": {"coefs": {"0": 1}, "op": "<", "value": 5}, "target": 6},
        {"id": 3, "op": "assert",
         "cond": {"coefs": {"0": 1, "1": -1}, "op": "==", "value": 0}},
        {"id": 4, "op": "assert",
         "cond": {"coefs": {"0": 1}, "op": "<=", "value": 5}},
        {"id": 5, "op": "halt"},
        {"id": 6, "op": "add", "reg": 0, "value": 1},
        {"id": 7, "op": "add", "reg": 1, "value": 1},
        {"id": 8, "op": "goto", "target": 2},
    ],
}

# 不可证断言:应返回 fail,首个未证位置为程序点 2
FAIL_CASE = {
    "num_registers": 1,
    "initial": [{"lo": 0, "hi": 0}],
    "instructions": [
        {"id": 0, "op": "set", "reg": 0, "value": 0},
        {"id": 1, "op": "add", "reg": 0, "value": 5},
        {"id": 2, "op": "assert",
         "cond": {"coefs": {"0": 1}, "op": "<=", "value": 3}},
        {"id": 3, "op": "halt"},
    ],
}

# 四类结构错误:寄存器越界 + 跳转悬空 + 不可解析约束 + 无可达终止,应合并反馈
ERROR_CASE = {
    "num_registers": 2,
    "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
    "instructions": [
        {"id": 0, "op": "set", "reg": 5, "value": 1},
        {"id": 1, "op": "goto", "target": 9},
        {"id": 2, "op": "assert",
         "cond": {"coefs": {"0": 2}, "op": "<=", "value": 1}},
        {"id": 3, "op": "goto", "target": 2},
    ],
}


def steering_guard_case(assert_op):
    """转向保护脚本:x0 ∈ [-1,1],非零进入转向包线检查,零值直接终止。"""
    return {
        "num_registers": 1,
        "initial": [{"lo": -1, "hi": 1}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "!=", "value": 0}, "target": 2},
            {"id": 1, "op": "halt"},
            {"id": 2, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": assert_op, "value": 0}},
            {"id": 3, "op": "halt"},
        ],
    }


# 危险正值:非零分支接 assert x0 <= 0 —— 正值超包线,必须失败
DANGER_CASE = steering_guard_case("<=")
# 安全非零:同一非零分支接 assert x0 != 0 —— 两向都满足,应放行
SAFE_NONZERO_CASE = steering_guard_case("!=")

_failures = []


def check(name, ok, detail=""):
    mark = "PASS" if ok else "FAIL"
    print(f"[{mark}] {name}" + (f" -- {detail}" if detail and not ok else ""))
    if not ok:
        _failures.append(name)


def request(method, path, payload=None):
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(APP_URL + path, data=data, method=method,
                                 headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=5) as resp:
            return resp.status, json.loads(resp.read())
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read())


def wait_ready():
    deadline = time.time() + WAIT_SECONDS
    while time.time() < deadline:
        try:
            code, body = request("GET", "/health")
            if code == 200 and body.get("status") == "ok":
                return body
        except (OSError, ValueError):
            pass
        time.sleep(0.5)
    return None


def main():
    health = wait_ready()
    check("health endpoint reachable", health is not None)
    if health is None:
        return 1

    # 镜像构建核对:运行中的镜像须报告期望的构建版本
    check("image build version matches",
          health.get("version") == EXPECTED_VERSION,
          f"expected {EXPECTED_VERSION}, got {health.get('version')!r}")

    code, body = request("POST", "/audit", PASS_CASE)
    check("pass case verdict", code == 200 and body.get("verdict") == "pass",
          f"code={code} body={body}")
    check("pass case post-fixpoint verified",
          body.get("fixpoint", {}).get("post_fixpoint_verified") is True)
    check("pass case per-point invariants present",
          "2" in body.get("points", {}) and
          any(c["text"] == "x0 - x1 <= 0" for c in body["points"]["3"]["invariant"]))

    code, body = request("POST", "/audit", FAIL_CASE)
    first = body.get("first_unproven", {})
    check("fail case verdict", code == 200 and body.get("verdict") == "fail",
          f"code={code} body={body}")
    check("fail case first unproven point", first.get("point") == 2)
    check("fail case is abstract alarm, not counterexample",
          first.get("kind") == "abstract_alarm")
    check("fail case uncovered envelope bound",
          bool(first.get("uncovered")) and first["uncovered"][0].get("bound") == 5)

    code, body = request("POST", "/audit", DANGER_CASE)
    first = body.get("first_unproven", {})
    check("danger case verdict is fail (no false pass)",
          code == 200 and body.get("verdict") == "fail",
          f"code={code} body={body}")
    check("danger case guard point is reachable",
          body.get("points", {}).get("2", {}).get("reachable") is True)
    check("danger case first unproven point stable at 2",
          first.get("point") == 2)
    check("danger case is abstract alarm, not counterexample",
          first.get("kind") == "abstract_alarm")
    check("danger case abstract boundary includes positive side x0 <= 1",
          any(c.get("text") == "x0 <= 1"
              for c in first.get("abstract_state", [])))
    check("danger case uncovered envelope bound (1 > required 0)",
          bool(first.get("uncovered")) and
          first["uncovered"][0].get("bound") == 1 and
          first["uncovered"][0].get("required") == 0)

    code, body = request("POST", "/audit", SAFE_NONZERO_CASE)
    check("safe nonzero case verdict is pass",
          code == 200 and body.get("verdict") == "pass",
          f"code={code} body={body}")
    check("safe nonzero case point is reachable (not marked unreachable)",
          body.get("points", {}).get("2", {}).get("reachable") is True)
    entry_checks = body.get("assertions", [{}])[0].get("entry_checks", [])
    guards = {c.get("branch", {}).get("guard") for c in entry_checks}
    check("safe nonzero case keeps both positive and negative directions",
          guards == {"x0 <= -1", "-x0 <= -1"} and
          all(c.get("implied") for c in entry_checks),
          f"guards={guards}")

    code, body = request("POST", "/audit", ERROR_CASE)
    kinds = {e.get("kind") for e in body.get("errors", [])}
    check("error case verdict", code == 200 and body.get("verdict") == "error",
          f"code={code} body={body}")
    check("error case merges all four structural kinds",
          {"register_out_of_bounds", "dangling_jump",
           "unparseable_constraint", "no_reachable_halt"} <= kinds,
          f"kinds={kinds}")
    check("error case returns no stale evidence",
          "points" not in body and "assertions" not in body)

    # 无状态性:结构错误之后再次审计,结论不受既往请求影响
    code, body = request("POST", "/audit", PASS_CASE)
    check("no stale state after error case",
          code == 200 and body.get("verdict") == "pass")

    if _failures:
        print(f"smoke FAILED: {len(_failures)} check(s): {', '.join(_failures)}")
        return 1
    print("smoke OK: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
