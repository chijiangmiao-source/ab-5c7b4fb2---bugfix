"""保护脚本的解析、结构校验与控制流图。

指令集(每条指令携带稳定编号 id,必须恰好为 0..N-1):
    set    : {"op":"set","reg":i,"value":c}        常量赋值
    add/sub: {"op":"add","reg":i,"value":c}        常量增减(sub 为取负别名)
    branch : {"op":"branch","cond":C,"target":t}   比较分支(假分支顺序下落)
    goto   : {"op":"goto","target":t}              无条件跳转
    assert : {"op":"assert","cond":C}              包线断言
    halt   : {"op":"halt"}                         终止

条件 C = {"coefs": {"<reg>": ±1, ...}, "op": 比较符, "value": 整数},
表示 sum(coef * x_reg) <op> value;比较符 ∈ <= < >= > == !=,至多两项
(八边形片段)。解析时统一规范化为 le / eq / ne 三种形态。

结构错误(寄存器越界、跳转悬空、不可解析约束、无可达终止等)全部收集后
合并反馈,不做任何分析计算。
"""
from __future__ import annotations

from dataclasses import dataclass

from .octagon import neg_terms, terms_text

MAX_REGISTERS = 4
MAX_INSTRUCTIONS = 48
COMPARE_OPS = ("<=", "<", ">=", ">", "==", "!=")
EXIT = "exit"  # 虚拟终止程序点:halt 或顺序走出脚本末尾均到达此处

OPS = ("set", "add", "sub", "branch", "goto", "assert", "halt")
_KIND_SYMBOL = {"le": "<=", "eq": "==", "ne": "!="}


def _is_int(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


@dataclass(frozen=True)
class Cond:
    """规范化条件:sum(terms) <kind> k,kind ∈ le/eq/ne。"""

    terms: tuple  # ((coef, reg), ...) 按 reg 升序,coef ∈ {+1,-1},0..2 项
    kind: str
    k: int
    text: str


@dataclass
class Instr:
    id: int
    op: str
    reg: "int | None" = None
    value: "int | None" = None
    cond: "Cond | None" = None
    target: "int | None" = None


@dataclass
class Edge:
    src: object
    dst: object
    kind: str  # fallthrough / branch_true / branch_false / goto / halt
    action: tuple  # ("none",) | ("set", r, c) | ("add", r, c) | ("guard", meets)


@dataclass
class Program:
    nregs: int
    initial: list  # [(lo, hi)],lo/hi 为 int 或 None(无界)
    instrs: list
    edges: list
    asserts: dict  # 程序点 -> Cond
    widening_points: set
    n_instr: int

    @property
    def points(self) -> list:
        return list(range(self.n_instr)) + [EXIT]


# ----------------------------------------------------------------------
# 条件解析
# ----------------------------------------------------------------------
def _parse_cond(raw, nregs: int, point, errors) -> "Cond | None":
    def bad(detail):
        errors.append({"kind": "unparseable_constraint", "point": point, "detail": detail})

    if not isinstance(raw, dict):
        bad("condition must be an object")
        return None
    coefs = raw.get("coefs")
    op = raw.get("op")
    value = raw.get("value")
    ok = True
    if not isinstance(coefs, dict):
        bad("'coefs' must be an object mapping register index to +1/-1")
        coefs = {}
        ok = False
    if op not in COMPARE_OPS:
        bad(f"'op' must be one of {list(COMPARE_OPS)}")
        ok = False
    if not _is_int(value):
        bad("'value' must be an integer")
        ok = False
    terms = []
    if isinstance(coefs, dict):
        if len(coefs) > 2:
            bad("at most two terms are allowed (octagon fragment)")
            ok = False
        for key, coef in coefs.items():
            try:
                reg = int(key)
            except (TypeError, ValueError):
                bad(f"register key {key!r} is not an integer")
                ok = False
                continue
            if not _is_int(coef) or coef not in (1, -1):
                bad(f"coefficient for register {reg} must be +1 or -1")
                ok = False
                continue
            if reg < 0 or reg >= nregs:
                errors.append({"kind": "register_out_of_bounds", "point": point, "register": reg})
                ok = False
                continue
            terms.append((coef, reg))
    if not ok:
        return None
    regs = [r for _, r in terms]
    if len(set(regs)) != len(regs):
        bad("duplicate register in 'coefs'")
        return None
    terms.sort(key=lambda t: t[1])
    # 规范化到 le / eq / ne(整数域:< 与 > 通过 ±1 吸收)
    if op == "<=":
        kind, k, nterms = "le", value, terms
    elif op == "<":
        kind, k, nterms = "le", value - 1, terms
    elif op == ">=":
        kind, k, nterms = "le", -value, neg_terms(tuple(terms))
    elif op == ">":
        kind, k, nterms = "le", -value - 1, neg_terms(tuple(terms))
    elif op == "==":
        kind, k, nterms = "eq", value, terms
    else:
        kind, k, nterms = "ne", value, terms
    nterms = tuple(sorted(nterms, key=lambda t: t[1]))
    text = f"{terms_text(nterms)} {_KIND_SYMBOL[kind]} {k}"
    return Cond(nterms, kind, k, text)


# ----------------------------------------------------------------------
# 指令解析
# ----------------------------------------------------------------------
def _parse_instr(raw, pos: int, nregs: int, errors) -> "Instr | None":
    if not isinstance(raw, dict):
        errors.append({"kind": "unparseable_instruction", "point": pos,
                       "detail": "instruction must be an object"})
        return None
    ident = raw.get("id")
    if not _is_int(ident):
        errors.append({"kind": "unparseable_instruction", "point": pos,
                       "detail": "'id' must be an integer"})
        return None
    op = raw.get("op")
    if op not in OPS:
        errors.append({"kind": "unparseable_instruction", "point": ident,
                       "detail": f"unknown op {op!r}"})
        return None
    ins = Instr(id=ident, op=op)
    if op in ("set", "add", "sub"):
        reg = raw.get("reg")
        value = raw.get("value")
        ok = True
        if not _is_int(reg):
            errors.append({"kind": "unparseable_instruction", "point": ident,
                           "detail": "'reg' must be an integer"})
            ok = False
        elif not (0 <= reg < nregs):
            errors.append({"kind": "register_out_of_bounds", "point": ident, "register": reg})
            ok = False
        if not _is_int(value):
            errors.append({"kind": "unparseable_instruction", "point": ident,
                           "detail": "'value' must be an integer"})
            ok = False
        if ok:
            ins.reg = reg
            ins.value = -value if op == "sub" else value
            ins.op = "add" if op == "sub" else op
    elif op in ("goto", "branch"):
        target = raw.get("target")
        if not _is_int(target):
            errors.append({"kind": "unparseable_instruction", "point": ident,
                           "detail": "'target' must be an integer"})
        else:
            ins.target = target
        if op == "branch":
            ins.cond = _parse_cond(raw.get("cond"), nregs, ident, errors)
    elif op == "assert":
        ins.cond = _parse_cond(raw.get("cond"), nregs, ident, errors)
    return ins


def _parse_initial(raw, nregs, errors) -> list:
    if not isinstance(raw, list) or (nregs is not None and len(raw) != nregs):
        errors.append({"kind": "invalid_initial_range",
                       "detail": "'initial' must be a list with one {lo, hi} entry per register"})
        return []
    initial = []
    for idx, ent in enumerate(raw):
        if not isinstance(ent, dict):
            errors.append({"kind": "invalid_initial_range", "register": idx,
                           "detail": "entry must be an object"})
            initial.append((None, None))
            continue
        lo, hi = ent.get("lo"), ent.get("hi")
        bad = False
        if lo is not None and not _is_int(lo):
            errors.append({"kind": "invalid_initial_range", "register": idx,
                           "detail": "'lo' must be an integer or null"})
            bad = True
        if hi is not None and not _is_int(hi):
            errors.append({"kind": "invalid_initial_range", "register": idx,
                           "detail": "'hi' must be an integer or null"})
            bad = True
        if not bad and lo is not None and hi is not None and lo > hi:
            errors.append({"kind": "invalid_initial_range", "register": idx, "detail": "lo > hi"})
            bad = True
        initial.append((None, None) if bad else (lo, hi))
    return initial


# ----------------------------------------------------------------------
# 控制流图
# ----------------------------------------------------------------------
def _guard_meets(cond: Cond, sense: bool):
    """分支条件在真/假方向上的单个八边形收窄项列表;None 表示该方向不可行。

    != 的真方向是析取(e <= k-1 或 -e <= -k-1),由 _guard_action 单独
    构造并集迁移;== 的假方向不是八边形约束,按恒等(不收窄)处理,保持可靠。
    """
    terms, kind, k = cond.terms, cond.kind, cond.k
    if not terms:  # 常量条件直接求值
        val = {"le": 0 <= k, "eq": 0 == k, "ne": 0 != k}[kind]
        feasible = val if sense else not val
        return () if feasible else None
    neg = neg_terms(terms)
    if kind == "le":
        return ((terms, k),) if sense else ((neg, -k - 1),)
    if kind == "eq":
        return ((terms, k), (neg, -k)) if sense else ()
    # kind == "ne"
    return () if sense else ((terms, k), (neg, -k))


def _guard_action(cond: Cond, sense: bool):
    """构造一条分支方向上的迁移。

    != 的真方向不是单个八边形约束:以两个八边形收窄的并集迁移处理
    (e <= k-1 或 -e <= -k-1),保证正负两个取值方向都不被丢弃;
    == 的假方向(e != k)同样不可表示为单个八边形约束,按恒等
    (不收窄)处理,保持可靠。
    """
    if sense and cond.kind == "ne" and cond.terms:
        terms = cond.terms
        alternatives = (
            ((terms, cond.k - 1),),
            ((neg_terms(terms), -cond.k - 1),),
        )
        return ("guard_disjunction", alternatives)
    meets = _guard_meets(cond, sense)
    if meets is None:
        return None
    return ("guard", meets)


def _build_edges(instrs: list, n_instr: int, errors: list) -> list:
    edges = []
    for ins in instrs:
        i = ins.id
        nxt = i + 1 if i + 1 < n_instr else EXIT
        op = ins.op
        if op in ("set", "add"):
            if ins.reg is None or ins.value is None:
                action = ("none",)  # 指令已报错,仅为可达性分析保留通路
            else:
                action = (op, ins.reg, ins.value)
            edges.append(Edge(i, nxt, "fallthrough", action))
        elif op == "assert":
            edges.append(Edge(i, nxt, "fallthrough", ("none",)))
        elif op == "halt":
            edges.append(Edge(i, EXIT, "halt", ("none",)))
        elif op == "goto":
            if ins.target is None:
                continue
            if not (0 <= ins.target < n_instr):
                errors.append({"kind": "dangling_jump", "point": i, "target": ins.target})
                continue
            edges.append(Edge(i, ins.target, "goto", ("none",)))
        elif op == "branch":
            tgt_ok = ins.target is not None and 0 <= ins.target < n_instr
            if ins.target is not None and not tgt_ok:
                errors.append({"kind": "dangling_jump", "point": i, "target": ins.target})
            if ins.cond is not None:
                true_action = _guard_action(ins.cond, True)
                false_action = _guard_action(ins.cond, False)
            else:  # 条件已报错,两个方向均按恒等放行以保证可达性检查完整
                true_action = false_action = ("guard", ())
            if tgt_ok and true_action is not None:
                edges.append(Edge(i, ins.target, "branch_true", true_action))
            if false_action is not None:
                edges.append(Edge(i, nxt, "branch_false", false_action))
    return edges


def _check_termination(edges: list, errors: list) -> None:
    out = {}
    for e in edges:
        out.setdefault(e.src, []).append(e.dst)
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in out.get(u, ()):
            if v not in seen:
                seen.add(v)
                stack.append(v)
    if EXIT not in seen:
        errors.append({"kind": "no_reachable_halt",
                       "detail": "no path from instruction 0 reaches 'halt' or the end of the script"})


def _widening_points(edges: list) -> set:
    """DFS 回边目标即为 widening 作用点(每个循环至少覆盖一个)。"""
    out = {}
    for e in edges:
        out.setdefault(e.src, []).append(e.dst)
    color = {0: 1}  # 1=灰(在栈上) 2=黑
    widening = set()
    stack = [(0, iter(out.get(0, ())))]
    while stack:
        node, it = stack[-1]
        nxt = None
        for v in it:
            nxt = v
            break
        if nxt is None:
            color[node] = 2
            stack.pop()
            continue
        c = color.get(nxt, 0)
        if c == 0:
            color[nxt] = 1
            stack.append((nxt, iter(out.get(nxt, ()))))
        elif c == 1:
            widening.add(nxt)
    return widening


# ----------------------------------------------------------------------
# 顶层入口
# ----------------------------------------------------------------------
def parse_program(payload):
    """返回 (Program, []) 或 (None, 合并后的结构错误列表)。"""
    errors = []
    if not isinstance(payload, dict):
        return None, [{"kind": "unparseable_program", "detail": "top level must be a JSON object"}]

    nregs_raw = payload.get("num_registers")
    nregs_ok = _is_int(nregs_raw) and 1 <= nregs_raw <= MAX_REGISTERS
    if not _is_int(nregs_raw):
        errors.append({"kind": "invalid_register_count", "detail": "'num_registers' must be an integer"})
    elif not nregs_ok:
        errors.append({"kind": "invalid_register_count",
                       "detail": f"'num_registers' must be within 1..{MAX_REGISTERS}",
                       "value": nregs_raw})
    nregs = nregs_raw if nregs_ok else MAX_REGISTERS  # 越界时仍继续收集其余错误

    initial = _parse_initial(payload.get("initial"),
                             nregs_raw if _is_int(nregs_raw) else None, errors)

    instrs_raw = payload.get("instructions")
    instrs = []
    n_instr = 0
    if not isinstance(instrs_raw, list) or not instrs_raw:
        errors.append({"kind": "invalid_instruction_count",
                       "detail": "'instructions' must be a non-empty list"})
    else:
        n_instr = len(instrs_raw)
        if n_instr > MAX_INSTRUCTIONS:
            errors.append({"kind": "invalid_instruction_count",
                           "detail": f"at most {MAX_INSTRUCTIONS} instructions allowed",
                           "count": n_instr})
        seen = set()
        for pos, raw in enumerate(instrs_raw):
            ins = _parse_instr(raw, pos, nregs, errors)
            if ins is None:
                continue
            if ins.id in seen:
                errors.append({"kind": "invalid_instruction_ids", "detail": f"duplicate id {ins.id}"})
                continue
            seen.add(ins.id)
            instrs.append(ins)
        expected = set(range(n_instr))
        if seen != expected:
            errors.append({"kind": "invalid_instruction_ids",
                           "detail": f"instruction ids must be exactly 0..{n_instr - 1}",
                           "missing": sorted(expected - seen),
                           "extra": sorted(i for i in seen if i not in expected)})
        instrs.sort(key=lambda i: i.id)

    edges = []
    if n_instr:
        edges = _build_edges(instrs, n_instr, errors)
        _check_termination(edges, errors)

    if errors:
        return None, errors

    asserts = {ins.id: ins.cond for ins in instrs if ins.op == "assert"}
    prog = Program(
        nregs=nregs,
        initial=initial,
        instrs=instrs,
        edges=edges,
        asserts=asserts,
        widening_points=_widening_points(edges),
        n_instr=n_instr,
    )
    return prog, []
