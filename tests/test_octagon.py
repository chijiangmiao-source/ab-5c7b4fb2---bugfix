"""八边形域单元测试:闭包、迁移函数、格运算与规范化输出。"""
import unittest

from app.octagon import INF, Octagon


class TestClosure(unittest.TestCase):
    def test_transitive_closure(self):
        o = Octagon(3)
        o.meet(((1, 0), (-1, 1)), 1)  # x0 - x1 <= 1
        o.meet(((1, 1), (-1, 2)), 2)  # x1 - x2 <= 2
        self.assertEqual(o.bound(((1, 0), (-1, 2))), 3)

    def test_strong_closure_integer_floor(self):
        o = Octagon(2)
        o.meet(((1, 0), (1, 1)), 1)   # x0 + x1 <= 1
        o.meet(((1, 0), (-1, 1)), 0)  # x0 - x1 <= 0  ⇒ 2*x0 <= 1
        self.assertEqual(o.bound(((1, 0),)), 0)  # 整数变量:x0 <= 0

    def test_meet_infeasible(self):
        o = Octagon(1)
        o.meet(((1, 0),), 3)    # x0 <= 3
        o.meet(((-1, 0),), -5)  # x0 >= 5
        self.assertTrue(o.empty)

    def test_self_bound_from_binary(self):
        o = Octagon(2)
        o.meet(((1, 0), (-1, 1)), 2)   # x0 - x1 <= 2
        o.meet(((-1, 0), (1, 1)), -2)  # x1 - x0 <= -2 ⇒ x0 = x1 + 2
        self.assertEqual(o.bound(((1, 0), (-1, 1))), 2)
        self.assertEqual(o.bound(((-1, 0), (1, 1))), -2)


class TestTransfer(unittest.TestCase):
    def test_assign_forgets_old_relation(self):
        o = Octagon(2)
        o.meet(((1, 0), (-1, 1)), 2)
        o.assign_const(0, 5)
        self.assertEqual(o.bound(((1, 0),)), 5)
        self.assertEqual(o.bound(((-1, 0),)), -5)
        self.assertEqual(o.bound(((1, 0), (-1, 1))), INF)

    def test_assign_keeps_other_registers(self):
        o = Octagon(2)
        o.meet(((1, 1),), 7)
        o.assign_const(0, 1)
        self.assertEqual(o.bound(((1, 1),)), 7)

    def test_shift_preserves_relation(self):
        o = Octagon(2)
        o.meet(((1, 0), (-1, 1)), 2)  # x0 - x1 <= 2
        o.shift_const(0, 3)           # x0 := x0 + 3
        self.assertEqual(o.bound(((1, 0), (-1, 1))), 5)

    def test_shift_negative(self):
        o = Octagon(1)
        o.meet(((1, 0),), 10)
        o.shift_const(0, -4)
        self.assertEqual(o.bound(((1, 0),)), 6)


class TestLattice(unittest.TestCase):
    def test_join_and_incl(self):
        a = Octagon(1)
        a.meet(((1, 0),), 3)
        b = Octagon(1)
        b.meet(((1, 0),), 7)
        j = a.join(b)
        self.assertEqual(j.bound(((1, 0),)), 7)
        self.assertTrue(a.incl(j))
        self.assertFalse(j.incl(a))

    def test_join_preserves_shared_relation(self):
        a = Octagon(2)
        a.meet(((1, 0), (-1, 1)), 0)
        a.meet(((1, 0),), 1)
        b = Octagon(2)
        b.meet(((1, 0), (-1, 1)), 0)
        b.meet(((1, 0),), 9)
        j = a.join(b)
        self.assertEqual(j.bound(((1, 0), (-1, 1))), 0)
        self.assertEqual(j.bound(((1, 0),)), 9)

    def test_widen_grown_component_goes_top(self):
        a = Octagon(1)
        a.meet(((1, 0),), 3)
        b = Octagon(1)
        b.meet(((1, 0),), 5)
        self.assertEqual(a.widen(b).bound(((1, 0),)), INF)

    def test_widen_keeps_stable_component(self):
        a = Octagon(1)
        a.meet(((1, 0),), 3)
        a.meet(((-1, 0),), 0)
        b = Octagon(1)
        b.meet(((1, 0),), 5)
        b.meet(((-1, 0),), 0)
        w = a.widen(b)
        self.assertEqual(w.bound(((1, 0),)), INF)
        self.assertEqual(w.bound(((-1, 0),)), 0)

    def test_meet_with(self):
        a = Octagon(1)
        a.meet(((1, 0),), 3)
        b = Octagon(1)
        b.meet(((1, 0),), 7)
        self.assertEqual(a.meet_with(b).bound(((1, 0),)), 3)


class TestCanonical(unittest.TestCase):
    def test_canonical_lists_all_finite_bounds(self):
        o = Octagon(2)
        o.meet(((1, 0), (1, 1)), 4)
        o.meet(((1, 0),), 2)
        texts = [c["text"] for c in o.canonical()]
        self.assertIn("x0 + x1 <= 4", texts)
        self.assertIn("x0 <= 2", texts)
        self.assertEqual(texts, sorted(texts))

    def test_canonical_machine_readable(self):
        o = Octagon(2)
        o.meet(((1, 0), (-1, 1)), 3)
        entry = [c for c in o.canonical() if c["text"] == "x0 - x1 <= 3"]
        self.assertEqual(entry[0]["coefs"], {"0": 1, "1": -1})
        self.assertEqual(entry[0]["value"], 3)


if __name__ == "__main__":
    unittest.main()
