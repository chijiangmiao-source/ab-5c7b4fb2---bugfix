"""不动点分析引擎:八边形域上的上升(widening)/下降(持续复算)迭代与断言判定。

流程:
  1. 结构校验(失败则合并反馈,不产生任何分析证据);
  2. 上升迭代:混沌工作集算法,回边目标处施加固定规则 widening,保证终止;
  3. 下降复算:自后不动点出发按 Gauss-Seidel 次序反复重算各点并取交,
     逐步回收 widening 损失的精度,每一步都仍是后不动点;
  4. 终态校验:逐条转移显式复核 f(inv[p]) ⊑ inv[q],确保输出确实为
     归纳不变量,调用方可凭响应中的逐点约束与入边来源独立重放该检查;
  5. 断言判定:每个可达断言须被该点不变量蕴含,否则按程序点编号给出
     首个未证位置、进入该点的抽象边界与未被涵盖的包线条件(抽象告警,
     不伪称具体执行反例)。
"""
from __future__ import annotations

from collections import deque

from .octagon import INF, Octagon, neg_terms, terms_text
from .program import EXIT, parse_program

MAX_DESCENDING_PASSES = 8


def _apply_action(state: Octagon, action: tuple) -> "Octagon | None":
    """对一条出边施加迁移函数;结果为空(不可行)时返回 None。"""
    kind = action[0]
    out = state.copy()
    if kind == "set":
        out.assign_const(action[1], action[2])
    elif kind == "add":
        out.shift_const(action[1], action[2])
    elif kind == "guard":
        for terms, k in action[1]:
            out.meet(terms, k)
            if out.empty:
                return None
    elif kind == "guard_any":
        for alternative in action[1]:
            for terms, k in alternative:
                out.meet(terms, k)
                if out.empty:
                    return None
    return None if out.empty else out


class _Engine:
    def __init__(self, prog):
        self.prog = prog
        self.points = prog.points
        self.inv = {p: None for p in self.points}  # None 表示 ⊥(不可达)
        self.in_edges = {p: [] for p in self.points}
        self.out_edges = {p: [] for p in self.points}
        for e in prog.edges:
            self.out_edges[e.src].append(e)
            self.in_edges[e.dst].append(e)
        self.initial = self._initial_state()
        self.ascending_iterations = 0
        self.descending_passes = 0

    def _initial_state(self) -> Octagon:
        o = Octagon(self.prog.nregs)
        n = self.prog.nregs
        for i, (lo, hi) in enumerate(self.prog.initial):
            if hi is not None:
                o.m[i][n + i] = 2 * hi
            if lo is not None:
                o.m[n + i][i] = -2 * lo
        o.close()
        return o

    # ------------------------------------------------------------------
    # 上升:widening 作用于回边目标,保证稳定
    # ------------------------------------------------------------------
    def _ascending(self) -> None:
        inv = self.inv
        inv[0] = self.initial
        work = deque([0])
        in_work = {0}
        widen_at = self.prog.widening_points
        while work:
            p = work.popleft()
            in_work.discard(p)
            src = inv[p]
            if src is None:
                continue
            for e in self.out_edges[p]:
                y = _apply_action(src, e.action)
                if y is None:
                    continue
                q = e.dst
                old = inv[q]
                if old is None:
                    inv[q] = y
                else:
                    joined = old.join(y)
                    if joined.incl(old):
                        continue
                    inv[q] = old.widen(joined) if q in widen_at else joined
                if q not in in_work:
                    work.append(q)
                    in_work.add(q)
                self.ascending_iterations += 1

    # ------------------------------------------------------------------
    # 下降:widening 之后持续复算不变量,逐步回收精度
    # ------------------------------------------------------------------
    def _descending(self) -> None:
        inv = self.inv
        for _ in range(MAX_DESCENDING_PASSES):
            changed = False
            for q in self.points:
                cur = inv[q]
                if cur is None:
                    continue  # 不可达点保持 ⊥
                contrib = self.initial.copy() if q == 0 else None
                for e in self.in_edges[q]:
                    s = inv[e.src]
                    if s is None:
                        continue
                    y = _apply_action(s, e.action)
                    if y is None:
                        continue
                    contrib = y if contrib is None else contrib.join(y)
                if contrib is None:
                    continue
                new = contrib.meet_with(cur)
                if new.empty:
                    inv[q] = None
                    changed = True
                    continue
                if new.incl(cur) and cur.incl(new):
                    continue
                inv[q] = new
                changed = True
            self.descending_passes += 1
            if not changed:
                break

    # ------------------------------------------------------------------
    # 终态校验:逐条转移显式复核不变量保持性
    # ------------------------------------------------------------------
    def _verify(self) -> list:
        violations = []
        head = self.inv[0]
        if head is None or not self.initial.incl(head):
            violations.append({"from": "entry", "to": 0, "kind": "entry"})
        for p in self.points:
            src = self.inv[p]
            if src is None:
                continue
            for e in self.out_edges[p]:
                y = _apply_action(src, e.action)
                if y is None:
                    continue
                dst = self.inv[e.dst]
                if dst is None or not y.incl(dst):
                    violations.append({"from": p, "to": e.dst, "kind": e.kind})
        return violations

    def run(self) -> list:
        self._ascending()
        self._descending()
        return self._verify()


# ----------------------------------------------------------------------
# 断言蕴含判定
# ----------------------------------------------------------------------
def _bound_detail(state: Octagon, terms: tuple, k: int, disjunction: bool = False) -> dict:
    b = state.bound(terms) if terms else 0
    detail = {
        "text": f"{terms_text(terms)} <= {k}",
        "bound": None if b == INF else b,
        "required": k,
        "implied": b <= k,
    }
    if disjunction:
        detail["disjunction"] = True
    return detail


def _check_assertion(state: Octagon, cond) -> tuple:
    """返回 (是否被蕴含, 逐条件界信息)。!= 以两个析取支检查。"""
    terms, kind, k = cond.terms, cond.kind, cond.k
    if kind == "le":
        details = [_bound_detail(state, terms, k)]
        return details[0]["implied"], details
    if kind == "eq":
        details = [
            _bound_detail(state, terms, k),
            _bound_detail(state, neg_terms(terms), -k),
        ]
        return all(d["implied"] for d in details), details
    # ne:expr <= k-1 或 -expr <= -k-1 任一成立即蕴含
    details = [
        _bound_detail(state, terms, k - 1, disjunction=True),
        _bound_detail(state, neg_terms(terms), -k - 1, disjunction=True),
    ]
    return any(d["implied"] for d in details), details


# ----------------------------------------------------------------------
# 输出装配
# ----------------------------------------------------------------------
def _points_view(engine: _Engine) -> dict:
    out = {}
    for p in engine.points:
        state = engine.inv[p]
        incoming = []
        if p == 0:
            incoming.append({"from": "entry", "kind": "entry"})
        for e in engine.in_edges[p]:
            incoming.append({"from": e.src, "kind": e.kind})
        incoming.sort(key=lambda d: (str(d["from"]), d["kind"]))
        out[str(p)] = {
            "reachable": state is not None,
            "invariant": state.canonical() if state is not None else None,
            "incoming": incoming,
        }
    return out


def analyze(payload) -> dict:
    """审计入口:返回 pass / fail / error 三种结论之一。"""
    prog, errors = parse_program(payload)
    if errors:
        # 结构问题合并反馈;不附带任何(旧)分析证据
        return {"verdict": "error", "reason": "structural_errors", "errors": errors}

    engine = _Engine(prog)
    violations = engine.run()
    if violations:  # 理论上不发生;宁可报错也不放行
        return {"verdict": "error", "reason": "fixpoint_verification_failed",
                "violations": violations}

    assertions = []
    unproven = []
    for point in sorted(prog.asserts):
        cond = prog.asserts[point]
        state = engine.inv[point]
        if state is None:
            assertions.append({"point": point, "condition": cond.text, "status": "unreachable"})
            continue
        ok, details = _check_assertion(state, cond)
        assertions.append({
            "point": point,
            "condition": cond.text,
            "status": "proven" if ok else "unproven",
            "bounds": details,
        })
        if not ok:
            unproven.append((point, cond, state, details))

    response = {
        "verdict": "pass" if not unproven else "fail",
        "program": {"num_registers": prog.nregs, "num_instructions": prog.n_instr},
        "points": _points_view(engine),
        "assertions": assertions,
        "fixpoint": {
            "widening_points": sorted(prog.widening_points),
            "ascending_iterations": engine.ascending_iterations,
            "descending_passes": engine.descending_passes,
            "post_fixpoint_verified": True,
        },
    }
    if unproven:
        point, cond, state, details = min(unproven, key=lambda u: u[0])
        response["first_unproven"] = {
            "point": point,
            "condition": cond.text,
            "abstract_state": state.canonical(),
            "uncovered": [d for d in details if not d["implied"]],
            "kind": "abstract_alarm",
            "note": "抽象解释上近似告警:不变量无法蕴含该包线条件;"
                    "此处给出的是抽象边界信息,并非具体执行反例。",
        }
    return response
