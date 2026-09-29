"""分析器单元测试:放行、未证告警、结构错误合并、widening 后复算。"""
import unittest

from app.analyzer import analyze


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


def nonzero_protection_program(envelope_op):
    """姿态工程师脚本:x0 ∈ [-1,1];x0 != 0 时进入转向包线检查,零值终止。

    envelope_op 为包线断言比较符:"<=" 给出危险脚本(正值越界),
    "!=" 给出安全脚本(非零即合法)。
    """
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


class TestNonzeroEnvelope(unittest.TestCase):
    def test_positive_direction_fails_not_unreachable(self):
        # 危险脚本:正值 x0=1 确会进入点 2 且超出 x0 <= 0 包线
        res = analyze(nonzero_protection_program("<="))
        self.assertEqual(res["verdict"], "fail")
        # 点 2 必须可达,绝不能标为不可达而放行
        self.assertTrue(res["points"]["2"]["reachable"])
        self.assertTrue(res["points"]["1"]["reachable"])  # 零值终止方向仍在
        self.assertEqual(res["assertions"][0]["status"], "unproven")
        first = res["first_unproven"]
        self.assertEqual(first["point"], 2)  # 稳定编号:按程序点裁决
        self.assertEqual(first["kind"], "abstract_alarm")  # 抽象告警,不伪造反例
        self.assertIn("并非具体执行反例", first["note"])
        # 未覆盖正值方向的抽象边界:-1 <= x0 <= 1
        texts = [c["text"] for c in first["abstract_state"]]
        self.assertIn("x0 <= 1", texts)
        self.assertIn("-x0 <= 1", texts)
        # 包线要求 x0 <= 0,不变量实际只能给到 x0 <= 1
        self.assertEqual(len(first["uncovered"]), 1)
        self.assertEqual(first["uncovered"][0]["text"], "x0 <= 0")
        self.assertEqual(first["uncovered"][0]["bound"], 1)
        self.assertEqual(first["uncovered"][0]["required"], 0)

    def test_nonzero_branch_to_ne_envelope_passes_and_keeps_both_directions(self):
        # 安全脚本:非零分支直接接 x0 != 0 包线断言
        res = analyze(nonzero_protection_program("!="))
        self.assertEqual(res["verdict"], "pass")
        self.assertTrue(res["points"]["2"]["reachable"])
        self.assertEqual(res["assertions"][0]["status"], "proven")
        # 凸包不变量为完整的 -1 <= x0 <= 1(两个方向都未被分析丢弃)
        texts = [c["text"] for c in res["points"]["2"]["invariant"]]
        self.assertEqual(set(texts), {"x0 <= 1", "-x0 <= 1"})
        # 证明来自逐入边分量:!= 真方向的两支(负支、正支)都须满足
        comps = res["assertions"][0]["component_bounds"]
        self.assertEqual(len(comps), 2)
        self.assertTrue(all(c["implied"] for c in comps))
        comp_texts = [[d["text"] for d in c["invariant"]] for c in comps]
        self.assertTrue(any("x0 <= -1" in t for t in comp_texts))   # 负方向支:x0 == -1
        self.assertTrue(any("-x0 <= -1" in t for t in comp_texts))  # 正方向支:x0 == 1

    def test_ne_true_edge_two_register_difference(self):
        res = analyze({
            "num_registers": 2,
            "initial": [{"lo": 0, "hi": 1}, {"lo": 0, "hi": 1}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"0": 1, "1": -1}, "op": "!=", "value": 0},
                 "target": 2},
                {"id": 1, "op": "halt"},
                {"id": 2, "op": "assert",
                 "cond": {"coefs": {"0": 1, "1": -1}, "op": "!=", "value": 0}},
                {"id": 3, "op": "halt"},
            ],
        })
        self.assertEqual(res["verdict"], "pass")
        self.assertTrue(res["points"]["2"]["reachable"])
        self.assertTrue(res["points"]["1"]["reachable"])

    def test_ne_in_loop_with_widening(self):
        # x0 从 0 自增,x0 != 3 时继续循环;出循环点 x0 <= 3 须可证,
        # 且 != 回边两支不破坏 widening 终止性与下降复算。
        res = analyze({
            "num_registers": 1,
            "initial": [{"lo": 0, "hi": 0}],
            "instructions": [
                {"id": 0, "op": "branch",
                 "cond": {"coefs": {"0": 1}, "op": "!=", "value": 3}, "target": 3},
                {"id": 1, "op": "assert",
                 "cond": {"coefs": {"0": 1}, "op": "<=", "value": 3}},
                {"id": 2, "op": "halt"},
                {"id": 3, "op": "add", "reg": 0, "value": 1},
                {"id": 4, "op": "goto", "target": 0},
            ],
        })
        self.assertEqual(res["verdict"], "pass")
        self.assertEqual(res["fixpoint"]["widening_points"], [0])
        self.assertGreaterEqual(res["fixpoint"]["descending_passes"], 1)
        self.assertTrue(res["fixpoint"]["post_fixpoint_verified"])


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
