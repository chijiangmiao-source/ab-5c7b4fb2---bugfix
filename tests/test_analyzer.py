"""分析器单元测试:放行、未证告警、结构错误合并、widening 后复算。"""
import unittest

from app.analyzer import analyze


def steering_guard_program(assert_op):
    """姿态工程师的转向保护脚本:x0 初始 [-1,1]。

        0: branch x0 != 0 -> 2   # 非零才进入转向包线检查
        1: halt                  # 零值直接终止
        2: assert <cond>         # 转向包线断言
        3: halt

    cond 为 x0 <= 0 时即"危险正值"脚本(正值超出包线);
    cond 为 x0 != 0 时即"安全非零"脚本(非零分支两向都满足)。
    """
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


def loop_relation_program():
    """x0 与 x1 同步自增的循环:区间域无法证明 x0==x1,八边形可以。"""
    return {
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


class TestPass(unittest.TestCase):
    def test_straight_line_pass(self):
        res = analyze({
            "num_registers": 2,
            "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "set", "reg": 0, "value": 1},
                {"id": 1, "op": "set", "reg": 1, "value": 2},
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 1, "1": 1}, "op": "<=", "value": 3}},
                {"id": 3, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "pass")
        self.assertEqual(res["assertions"][0]["status"], "proven")
        self.assertTrue(res["fixpoint"]["post_fixpoint_verified"])
        texts = [c["text"] for c in res["points"]["2"]["invariant"]]
        self.assertIn("x0 + x1 <= 3", texts)

    def test_loop_relation_pass_with_widening_and_recompute(self):
        res = analyze(loop_relation_program())
        self.assertEqual(res["verdict"], "pass")
        statuses = {a["point"]: a["status"] for a in res["assertions"]}
        self.assertEqual(statuses, {3: "proven", 4: "proven"})
        # 回边目标被识别为 widening 作用点
        self.assertEqual(res["fixpoint"]["widening_points"], [2])
        # widening 之后确有下降复算
        self.assertGreaterEqual(res["fixpoint"]["descending_passes"], 1)
        # 出循环后不变量精确到 x0 == x1 == 5
        texts = [c["text"] for c in res["points"]["3"]["invariant"]]
        self.assertIn("x0 - x1 <= 0", texts)
        self.assertIn("-x0 + x1 <= 0", texts)
        self.assertIn("x0 <= 5", texts)
        self.assertIn("-x0 <= -5", texts)

    def test_initial_ranges_respected(self):
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 2, "hi": 3}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": ">=", "value": 2}},
                {"id": 1, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 3}},
                {"id": 2, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "pass")

    def test_unreachable_assert_is_vacuous(self):
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"0": 1}, "op": ">=", "value": 1}, "target": 2},
                {"id": 1, "op": "halt"},
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": -1}},
                {"id": 3, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "pass")
        self.assertEqual(res["assertions"][0]["status"], "unreachable")
        self.assertFalse(res["points"]["2"]["reachable"])

    def test_falloff_end_counts_as_termination(self):
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 1, "hi": 1}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "==", "value": 1}},
            ],
        })
        self.assertEqual(res["verdict"], "pass")

    def test_incoming_edges_listed(self):
        res = analyze(loop_relation_program())
        kinds2 = {(e["from"], e["kind"]) for e in res["points"]["2"]["incoming"]}
        self.assertIn((1, "fallthrough"), kinds2)
        self.assertIn((8, "goto"), kinds2)
        kinds3 = {(e["from"], e["kind"]) for e in res["points"]["3"]["incoming"]}
        self.assertIn((2, "branch_false"), kinds3)
        kinds6 = {(e["from"], e["kind"]) for e in res["points"]["6"]["incoming"]}
        self.assertIn((2, "branch_true"), kinds6)
        self.assertIn(("entry", "entry"),
                      {(e["from"], e["kind"]) for e in res["points"]["0"]["incoming"]})


class TestFail(unittest.TestCase):
    def test_first_unproven_by_point_and_abstract_boundary(self):
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "set", "reg": 0, "value": 0},
                {"id": 1, "op": "add", "reg": 0, "value": 5},
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 3}},
                {"id": 3, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 2}},
                {"id": 4, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "fail")
        first = res["first_unproven"]
        # 首个按程序点编号稳定裁决的位置
        self.assertEqual(first["point"], 2)
        self.assertEqual(first["kind"], "abstract_alarm")
        self.assertIn("并非具体执行反例", first["note"])
        # 未被涵盖的包线条件:不变量只给到 x0 <= 5
        self.assertEqual(first["uncovered"][0]["bound"], 5)
        self.assertEqual(first["uncovered"][0]["required"], 3)
        # 进入该点的抽象边界
        texts = [c["text"] for c in first["abstract_state"]]
        self.assertIn("x0 <= 5", texts)

    def test_unbounded_initial_gives_null_bound(self):
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": None, "hi": None}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 5}},
                {"id": 1, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "fail")
        self.assertIsNone(res["first_unproven"]["uncovered"][0]["bound"])

    def test_branch_ne_false_edge_not_narrowed(self):
        # == 的假方向(即 !=)不是八边形约束,保持不收窄 → 无法证明 x0 >= 1
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": None, "hi": None}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"0": 1}, "op": "==", "value": 0}, "target": 3},
                {"id": 1, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": ">=", "value": 1}},
                {"id": 2, "op": "halt"},
                {"id": 3, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 0}},
                {"id": 4, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "fail")
        self.assertEqual(res["first_unproven"]["point"], 1)
        statuses = {a["point"]: a["status"] for a in res["assertions"]}
        self.assertEqual(statuses[3], "proven")  # == 的真方向精确收窄

    def test_ne_assertion_disjunction(self):
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "!=", "value": 0}},
                {"id": 1, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "fail")
        uncovered = res["first_unproven"]["uncovered"]
        self.assertEqual(len(uncovered), 2)
        self.assertTrue(all(d.get("disjunction") for d in uncovered))


class TestSteeringGuardAcceptance(unittest.TestCase):
    """姿态工程师转向保护脚本的两类核心验收:危险正值必须失败,安全非零放行。"""

    # -- 危险正值:x0 ∈ [-1,1],非零进入 assert x0 <= 0 --
    def test_dangerous_positive_value_fails(self):
        res = analyze(steering_guard_program("<="))
        # 必须返回失败,绝不允许"放行"
        self.assertEqual(res["verdict"], "fail")
        # 断言点必须可达——寄存器取正值确会进入该位置,不得标为不可达
        self.assertTrue(res["points"]["2"]["reachable"])
        self.assertEqual(res["assertions"][0]["status"], "unproven")

    def test_dangerous_positive_first_unproven_stable(self):
        res = analyze(steering_guard_program("<="))
        first = res["first_unproven"]
        # 首个未证断言稳定编号为程序点 2
        self.assertEqual(first["point"], 2)
        self.assertEqual(first["condition"], "x0 <= 0")
        # 抽象告警,不是伪造的具体反例
        self.assertEqual(first["kind"], "abstract_alarm")
        self.assertIn("并非具体执行反例", first["note"])

    def test_dangerous_positive_abstract_boundary_uncovers_positive(self):
        res = analyze(steering_guard_program("<="))
        first = res["first_unproven"]
        # 进入该点的抽象边界包含未被覆盖的正值方向 x0 <= 1 与负侧 -x0 <= 1
        texts = [c["text"] for c in first["abstract_state"]]
        self.assertIn("x0 <= 1", texts)
        self.assertIn("-x0 <= 1", texts)
        # 未涵盖的包线条件:不变量只能给到上界 1,包线要求 0
        self.assertEqual(len(first["uncovered"]), 1)
        u = first["uncovered"][0]
        self.assertEqual(u["text"], "x0 <= 0")
        self.assertEqual(u["bound"], 1)
        self.assertEqual(u["required"], 0)
        self.assertFalse(u["implied"])

    # -- 安全非零:同一非零分支接 assert x0 != 0 --
    def test_safe_nonzero_passes_and_point_reachable(self):
        res = analyze(steering_guard_program("!="))
        # 放行
        self.assertEqual(res["verdict"], "pass")
        # 程序点不能被标为不可达
        self.assertTrue(res["points"]["2"]["reachable"])
        self.assertEqual(res["assertions"][0]["status"], "proven")
        self.assertNotIn("first_unproven", res)

    def test_safe_nonzero_keeps_both_directions(self):
        res = analyze(steering_guard_program("!="))
        # 正负两个非零取值都不能因分析过程被丢弃:逐析取支证据须齐备且各自成立
        checks = res["assertions"][0]["entry_checks"]
        by_guard = {c["branch"]["guard"]: c for c in checks}
        self.assertEqual(set(by_guard), {"x0 <= -1", "-x0 <= -1"})
        self.assertTrue(all(c["implied"] for c in checks))
        self.assertTrue(all(c["from"] == 0 for c in checks))

    def test_diff_inequality_nonzero_branch_both_dirs_kept(self):
        # 双寄存器差值 x0 - x1 ∈ [-1,1] 的 != 分支同样保留正负两向
        payload = {
            "num_registers": 2,
            "initial": [{"lo": -1, "hi": 1}, {"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"0": 1, "1": -1}, "op": "!=", "value": 0},
                 "target": 2},
                {"id": 1, "op": "halt"},
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 1, "1": -1}, "op": "!=", "value": 0}},
                {"id": 3, "op": "halt"},
            ],
        }
        res = analyze(payload)
        self.assertEqual(res["verdict"], "pass")
        self.assertTrue(res["points"]["2"]["reachable"])
        guards = {c["branch"]["guard"] for c in res["assertions"][0]["entry_checks"]}
        self.assertEqual(guards, {"x0 - x1 <= -1", "-x0 + x1 <= -1"})

    def test_diff_inequality_positive_direction_uncovered(self):
        # 同一非零差值分支接差 <= 0:正差方向超包线,失败并给出上界 1
        payload = {
            "num_registers": 2,
            "initial": [{"lo": -1, "hi": 1}, {"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"0": 1, "1": -1}, "op": "!=", "value": 0},
                 "target": 2},
                {"id": 1, "op": "halt"},
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 1, "1": -1}, "op": "<=", "value": 0}},
                {"id": 3, "op": "halt"},
            ],
        }
        res = analyze(payload)
        self.assertEqual(res["verdict"], "fail")
        self.assertTrue(res["points"]["2"]["reachable"])
        self.assertEqual(res["first_unproven"]["point"], 2)
        self.assertEqual(res["first_unproven"]["uncovered"][0]["bound"], 1)


class TestStructuralErrors(unittest.TestCase):
    def test_merged_feedback_without_stale_evidence(self):
        res = analyze({
            "num_registers": 2,
            "initial": [{"lo": 0, "hi": 0}, {"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "set", "reg": 5, "value": 1},          # 寄存器越界
                {"id": 1, "op": "goto", "target": 9},                  # 跳转悬空
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 2}, "op": "<=", "value": 1}},  # 不可解析约束
                {"id": 3, "op": "goto", "target": 2},                  # 环内无终止
            ],
        })
        self.assertEqual(res["verdict"], "error")
        self.assertEqual(res["reason"], "structural_errors")
        kinds = {e["kind"] for e in res["errors"]}
        self.assertIn("register_out_of_bounds", kinds)
        self.assertIn("dangling_jump", kinds)
        self.assertIn("unparseable_constraint", kinds)
        self.assertIn("no_reachable_halt", kinds)
        # 合并反馈不附带任何分析证据
        self.assertNotIn("points", res)
        self.assertNotIn("first_unproven", res)
        self.assertNotIn("assertions", res)

    def test_no_reachable_halt_alone(self):
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [{"id": 0, "op": "goto", "target": 0}],
        })
        self.assertEqual(res["verdict"], "error")
        self.assertEqual([e["kind"] for e in res["errors"]], ["no_reachable_halt"])

    def test_limits(self):
        res = analyze({
            "num_registers": 5,
            "initial": [],
            "instructions": [{"id": 0, "op": "halt"}],
        })
        kinds = {e["kind"] for e in res["errors"]}
        self.assertIn("invalid_register_count", kinds)
        self.assertIn("invalid_initial_range", kinds)

        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [{"id": i, "op": "halt"} for i in range(49)],
        })
        kinds = {e["kind"] for e in res["errors"]}
        self.assertIn("invalid_instruction_count", kinds)

    def test_bad_ids(self):
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "halt"},
                {"id": 0, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "error")
        self.assertIn("invalid_instruction_ids", {e["kind"] for e in res["errors"]})


if __name__ == "__main__":
    unittest.main()
