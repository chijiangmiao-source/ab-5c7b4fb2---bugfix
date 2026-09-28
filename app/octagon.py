"""八边形抽象域:以差分界矩阵(DBM)精确表示 ±x_i ± x_j <= c 形式的约束。

字面量编码(共 2n 个,n 为寄存器数):
    下标 i      表示 +x_i    (0 <= i < n)
    下标 n + i  表示 -x_i
矩阵元素 m[a][b] 表示 lit_a - lit_b 的上界,取值为整数或 +∞。
一元约束 x_i <= c 以 2*x_i <= 2c 的形式存放于 m[i][n+i]。

所有寄存器均为整数,因此强闭包中的减半步骤向下取整(整值 tightening)。
"""
from __future__ import annotations

from math import inf

INF = inf


def neg_terms(terms: tuple) -> tuple:
    """对一组 (系数, 寄存器) 项整体取负。"""
    return tuple((-s, r) for s, r in terms)


def terms_text(terms: tuple) -> str:
    """把 ((coef, reg), ...) 渲染为可读表达式,如 "x0 - x1"。"""
    if not terms:
        return "0"
    text = ""
    for s, r in terms:
        name = f"x{r}"
        if not text:
            text = name if s == 1 else f"-{name}"
        else:
            text += f" {'+' if s == 1 else '-'} {name}"
    return text


def constraint_dict(terms: tuple, k: int) -> dict:
    """规范化约束的机器可读表示。"""
    return {
        "text": f"{terms_text(terms)} <= {k}",
        "coefs": {str(r): s for s, r in terms},
        "value": k,
    }


class Octagon:
    """一个程序点上的八边形不变量(始终处于强闭包形态,除非 empty)。"""

    __slots__ = ("n", "m", "empty")

    def __init__(self, n: int):
        self.n = n
        size = 2 * n
        self.m = [[INF] * size for _ in range(size)]
        for a in range(size):
            self.m[a][a] = 0
        self.empty = False

    # ------------------------------------------------------------------
    # 基础工具
    # ------------------------------------------------------------------
    def copy(self) -> "Octagon":
        o = Octagon.__new__(Octagon)
        o.n = self.n
        o.m = [row[:] for row in self.m]
        o.empty = self.empty
        return o

    def _bar(self, a: int) -> int:
        """字面量 a 的否定下标。"""
        return a + self.n if a < self.n else a - self.n

    # ------------------------------------------------------------------
    # 强闭包:Floyd-Warshall 最短路 + 八边形整值 tightening
    # ------------------------------------------------------------------
    def close(self) -> None:
        n = self.n
        m = self.m
        size = 2 * n
        for k in range(size):
            mk = m[k]
            for i in range(size):
                mi = m[i]
                via = mi[k]
                if via == INF:
                    continue
                for j in range(size):
                    w = mk[j]
                    if w == INF:
                        continue
                    s = via + w
                    if s < mi[j]:
                        mi[j] = s
        # 八边形 tightening:m[i][j] <= (m[i][bar(i)] + m[bar(j)][j]) / 2
        for i in range(size):
            bi = self._bar(i)
            mi = m[i]
            for j in range(size):
                a = mi[bi]
                b = m[self._bar(j)][j]
                if a == INF or b == INF:
                    continue
                t = (a + b) // 2  # 整数变量:向下取整仍精确
                if t < mi[j]:
                    mi[j] = t
        for a in range(size):
            if m[a][a] < 0:
                self.empty = True
                return
            m[a][a] = 0

    # ------------------------------------------------------------------
    # 迁移函数
    # ------------------------------------------------------------------
    def meet(self, terms: tuple, k: int) -> None:
        """加入约束 sum(coef * x_reg) <= k 并重新闭包。terms 为 0..2 项。"""
        n = self.n
        if not terms:
            if k < 0:  # 0 <= k 不成立 → 空
                self.empty = True
            return
        if len(terms) == 1:
            (s, i) = terms[0]
            a = i if s == 1 else n + i
            b = n + i if s == 1 else i
            if 2 * k < self.m[a][b]:
                self.m[a][b] = 2 * k
        else:
            (s1, i), (s2, j) = terms
            # expr <= k ⟺ lit(s1,i) - lit(-s2,j) <= k,两个对称书写都记录
            pairs = (
                (i if s1 == 1 else n + i, n + j if s2 == 1 else j),
                (j if s2 == 1 else n + j, n + i if s1 == 1 else i),
            )
            for a, b in pairs:
                if k < self.m[a][b]:
                    self.m[a][b] = k
        self.close()

    def assign_const(self, r: int, c: int) -> None:
        """x_r := c:先遗忘 x_r 的全部旧关系,再加入等式。"""
        n = self.n
        size = 2 * n
        for a in range(size):
            for b in range(size):
                if a == b:
                    self.m[a][b] = 0
                elif a == r or a == n + r or b == r or b == n + r:
                    self.m[a][b] = INF
        self.m[r][n + r] = 2 * c
        self.m[n + r][r] = -2 * c
        self.close()

    def shift_const(self, r: int, c: int) -> None:
        """x_r := x_r + c:对含 x_r 的界做平移,精确保留寄存器间关系。

        代入 old = new - c:
          行首为 +x_r 的界 +c,行首为 -x_r 的界 -c;
          行尾为 +x_r 的界 -c,行尾为 -x_r 的界 +c。
        """
        n = self.n
        size = 2 * n
        m = self.m
        for a in range(size):
            for b in range(size):
                v = m[a][b]
                if v == INF:
                    continue
                d = 0
                if a == r:
                    d += c
                elif a == n + r:
                    d -= c
                if b == r:
                    d -= c
                elif b == n + r:
                    d += c
                if d:
                    m[a][b] = v + d
        self.close()

    # ------------------------------------------------------------------
    # 格运算
    # ------------------------------------------------------------------
    def join(self, other: "Octagon") -> "Octagon":
        """八边形凸包:闭包 DBM 的逐分量 max 仍为闭包。"""
        o = Octagon(self.n)
        size = 2 * self.n
        for a in range(size):
            ma, mb, mo = self.m[a], other.m[a], o.m[a]
            for b in range(size):
                va, vb = ma[b], mb[b]
                mo[b] = va if va > vb else vb
        return o

    def meet_with(self, other: "Octagon") -> "Octagon":
        """交:逐分量 min 后重新闭包。"""
        o = Octagon(self.n)
        size = 2 * self.n
        for a in range(size):
            ma, mb, mo = self.m[a], other.m[a], o.m[a]
            for b in range(size):
                va, vb = ma[b], mb[b]
                mo[b] = va if va < vb else vb
        o.close()
        return o

    def widen(self, other: "Octagon") -> "Octagon":
        """固定规则 widening:凡相对 self 变弱(增大)的分量直接放宽到 +∞。"""
        o = Octagon(self.n)
        size = 2 * self.n
        for a in range(size):
            ma, mb, mo = self.m[a], other.m[a], o.m[a]
            for b in range(size):
                va, vb = ma[b], mb[b]
                mo[b] = va if vb <= va else INF
        return o

    def incl(self, other: "Octagon") -> bool:
        """self ⊑ other(逐分量比较;self 已闭包时即语义包含)。"""
        size = 2 * self.n
        for a in range(size):
            ma, mb = self.m[a], other.m[a]
            for b in range(size):
                if ma[b] > mb[b]:
                    return False
        return True

    # ------------------------------------------------------------------
    # 查询
    # ------------------------------------------------------------------
    def bound(self, terms: tuple) -> "int | float":
        """已闭包状态下表达式 sum(coef * x_reg) 的最紧上界(整数或 +∞)。"""
        n = self.n
        if not terms:
            return 0
        if len(terms) == 1:
            (s, i) = terms[0]
            v = self.m[i][n + i] if s == 1 else self.m[n + i][i]
            return INF if v == INF else v // 2
        (s1, i), (s2, j) = terms
        a1 = i if s1 == 1 else n + i
        b1 = n + j if s2 == 1 else j
        a2 = j if s2 == 1 else n + j
        b2 = n + i if s1 == 1 else i
        return min(self.m[a1][b1], self.m[a2][b2])

    def canonical(self) -> list:
        """规范化闭包约束:所有有限界以 <= 形式列出,按文本排序,便于独立复核。"""
        n = self.n
        out = []
        for i in range(n):
            hi = self.m[i][n + i]
            if hi != INF:
                out.append(constraint_dict(((1, i),), hi // 2))
            lo = self.m[n + i][i]
            if lo != INF:
                out.append(constraint_dict(((-1, i),), lo // 2))
        for i in range(n):
            for j in range(i + 1, n):
                candidates = (
                    (((1, i), (1, j)), min(self.m[i][n + j], self.m[j][n + i])),
                    (((1, i), (-1, j)), self.m[i][j]),
                    (((-1, i), (1, j)), self.m[j][i]),
                    (((-1, i), (-1, j)), min(self.m[n + i][j], self.m[n + j][i])),
                )
                for terms, v in candidates:
                    if v != INF:
                        out.append(constraint_dict(terms, v))
        out.sort(key=lambda d: d["text"])
        return out
