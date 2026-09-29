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

# 姿态保护脚本的公共骨架:x0 ∈ [-1,1];x0 != 0 进入转向包线检查,零值终止。
def _nonzero_program(envelope_op):
    return {
        "num_registers": 1,
        "initial": [{"lo": -1, "hi": 1}],
        "instructions": [
            {"id": 0, "op": "branch",
             "cond": {"coefs": {"0": 1}, "op": "!=", "value": 0}, "target": 2},
            {"id": 1, "op": "halt"},
            {"id": 2, "op": "assert",
             "cond": {"coefs": {"0": 1}, "op": envelope_op, "value": 0}},
            {"id": 3, "op": "halt"},
        ],
    }

# 危险正值:包线 x0 <= 0,正值 x0=1 确会进入点 2 且越界 → fail(抽象告警,非反例)
DANGER_CASE = _nonzero_program("<=")
# 安全非零:包线即 x0 != 0,非零分支两个方向都合法 → pass
SAFE_NONZERO_CASE = _nonzero_program("!=")

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

    # 危险正值脚本:非零分支后 x0 <= 0 包线,正值方向必须被稳定定位为未证,
    # 且程序点可达(不得标记不可达而放行),证据为抽象边界而非具体反例。
    code, body = request("POST", "/audit", DANGER_CASE)
    first = body.get("first_unproven", {})
    check("danger case verdict", code == 200 and body.get("verdict") == "fail",
          f"code={code} body={body}")
    check("danger case check point is reachable",
          body.get("points", {}).get("2", {}).get("reachable") is True)
    check("danger case zero-halt direction also reachable",
          body.get("points", {}).get("1", {}).get("reachable") is True)
    check("danger case first unproven point stable", first.get("point") == 2)
    check("danger case is abstract alarm", first.get("kind") == "abstract_alarm")
    state_texts = [c.get("text") for c in first.get("abstract_state", [])]
    check("danger case abstract boundary keeps positive direction",
          "x0 <= 1" in state_texts and "-x0 <= 1" in state_texts,
          f"state={state_texts}")
    uncovered = first.get("uncovered", [])
    check("danger case uncovered positive side x0 <= 0 with bound 1",
          len(uncovered) == 1 and uncovered[0].get("bound") == 1
          and uncovered[0].get("required") == 0,
          f"uncovered={uncovered}")

    # 安全非零脚本:非零分支直接接 x0 != 0 断言,应放行且点可达;
    # 正负两个非零取值都不得在分析中被丢弃。
    code, body = request("POST", "/audit", SAFE_NONZERO_CASE)
    check("safe nonzero case verdict", code == 200 and body.get("verdict") == "pass",
          f"code={code} body={body}")
    check("safe nonzero case point reachable",
          body.get("points", {}).get("2", {}).get("reachable") is True)
    assertion = body.get("assertions", [{}])[0]
    check("safe nonzero case assertion proven", assertion.get("status") == "proven")
    hull = [c.get("text") for c in body.get("points", {}).get("2", {}).get("invariant", [])]
    check("safe nonzero case hull keeps both nonzero directions",
          set(hull) == {"x0 <= 1", "-x0 <= 1"}, f"hull={hull}")
    comps = assertion.get("component_bounds", [])
    check("safe nonzero case both disjunct components prove it",
          len(comps) == 2 and all(c.get("implied") for c in comps),
          f"components={comps}")

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
