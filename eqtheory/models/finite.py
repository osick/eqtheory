"""Finite countermodels: a magma table on Fin n satisfying the hypothesis
and refuting the goal.

Five searches, cheapest first (the ladder in :func:`find_countermodel`):

1. **Exhaustive scan** of all n^(n²) tables for n ≤ 3 (:func:`scan`).
2. **Symbolic linear families** — scalar-affine (a·i + b·j + c) mod n up
   to n = 32 and matrix-linear over (ℤ_p)², both evaluated *symbolically*
   (coefficient vectors, no table enumeration) so the check is one
   evaluation per equation instead of n^k (:func:`linear_countermodel`).
3. **Structured tables** — projections, ±, max/min, shifts, affine,
   sparse (:func:`structured_tables`), bilinear tables and a seeded
   random sweep.
4. **Complete cell search** with watched instances, unit propagation and
   the Least Number Heuristic (:func:`find_model_cells`). Complete: an
   empty verdict is a proof that no Fin-n countermodel exists.
5. **CDCL** on a direct CNF encoding with a value-symmetry ladder
   (:func:`find_model_sat`); chosen automatically when the encoding fits
   in memory (:func:`decide_size`). Also complete.

The completeness verdicts (``SearchFacts.exhausted``) are worth as much
as the models: they cut the search space for every later stage and are
the sharpest hint an LLM stage can be given.
"""
from __future__ import annotations

import random
import time
from dataclasses import dataclass, field
from typing import Iterator

from ..config import settings
from ..terms import Equation, Term, evaluate, holds

MAX_TABLE_N = 10          # judge-style certificates only: finOpTable reads one digit per entry

Table = list


@dataclass(frozen=True)
class Countermodel:
    n: int
    table: Table

    def op(self, a: int, b: int) -> int:
        return self.table[a][b]

    def affine_form(self):
        """(a, b, c) with table[i][j] = (a·i + b·j + c) mod n, or None."""
        n, t = self.n, self.table
        c = t[0][0] % n
        a = (t[1][0] - c) % n if n > 1 else 0
        b = (t[0][1] - c) % n if n > 1 else 0
        for i in range(n):
            for j in range(n):
                if t[i][j] % n != (a * i + b * j + c) % n:
                    return None
        return a, b, c


@dataclass
class SearchFacts:
    """What a search *proved*: sizes with provably no countermodel, and
    sizes whose heuristic families were searched."""
    exhausted: list = field(default_factory=list)
    searched: list = field(default_factory=list)


def is_countermodel(hyp: Equation, goal: Equation, n: int, table: Table) -> bool:
    op = lambda a, b: table[a][b]
    return holds(hyp, op, n) and not holds(goal, op, n)


# ── 1. exhaustive scan ───────────────────────────────────────────────────

def scan(hyp: Equation, goal: Equation, max_n: int = 3):
    """Enumerate every table on Fin 2..max_n. Returns
    (countermodel_or_None, hypothesis_has_any_model)."""
    has_model = False
    for n in range(2, max_n + 1):
        for enc in range(n ** (n * n)):
            table, rem = [], enc
            for _ in range(n):
                row = []
                for _ in range(n):
                    row.append(rem % n); rem //= n
                table.append(row)
            op = lambda a, b, t=table: t[a][b]
            if not holds(hyp, op, n):
                continue
            has_model = True
            if not holds(goal, op, n):
                return Countermodel(n, table), True
    return None, has_model


# ── 2. symbolic linear families ──────────────────────────────────────────

def _linear_form_holds(eq: Equation, op, unit, zero_const, zero_coef) -> bool:
    """Evaluate both sides to (coefficient map, constant) and compare."""
    env = {v: ({v: unit}, zero_const) for v in eq.variables}
    L, R = evaluate(eq.lhs, op, env), evaluate(eq.rhs, op, env)
    if L[1] != R[1]:
        return False
    return all(L[0].get(v, zero_coef) == R[0].get(v, zero_coef) for v in set(L[0]) | set(R[0]))


def _affine_sweep(hyp, goal, n_max, deadline):
    for n in range(2, n_max + 1):
        if time.monotonic() > deadline:
            return None
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    def op(X, Y, a=a, b=b, c=c, n=n):
                        cs = {v: (a * X[0].get(v, 0) + b * Y[0].get(v, 0)) % n for v in set(X[0]) | set(Y[0])}
                        return (cs, (a * X[1] + b * Y[1] + c) % n)
                    if _linear_form_holds(hyp, op, 1 % n, 0, 0) and not _linear_form_holds(goal, op, 1 % n, 0, 0):
                        return Countermodel(n, [[(a * i + b * j + c) % n for j in range(n)] for i in range(n)])
    return None


def _matrix_linear_sweep(hyp, goal, primes, deadline):
    """op(u, v) = A·u + B·v + c over (ℤ_p)², elements encoded i = p·u₀ + u₁."""
    for p in primes:
        rng2 = range(2)
        mats = [((a, b), (c, d)) for a in range(p) for b in range(p) for c in range(p) for d in range(p)]
        vecs = [(u, v) for u in range(p) for v in range(p)]
        I, Z = ((1, 0), (0, 1)), ((0, 0), (0, 0))

        def matmul(A, B):
            return tuple(tuple(sum(A[i][k] * B[k][j] for k in rng2) % p for j in rng2) for i in rng2)

        def matvec(A, w):
            return tuple(sum(A[i][k] * w[k] for k in rng2) % p for i in rng2)

        for A in mats:
            if time.monotonic() > deadline:
                return None
            for B in mats:
                for cv in vecs:
                    def op(X, Y, A=A, B=B, cv=cv):
                        cs = {}
                        for v in set(X[0]) | set(Y[0]):
                            MA, MB = matmul(A, X[0].get(v, Z)), matmul(B, Y[0].get(v, Z))
                            cs[v] = tuple(tuple((MA[i][j] + MB[i][j]) % p for j in rng2) for i in rng2)
                        wa, wb = matvec(A, X[1]), matvec(B, Y[1])
                        return (cs, tuple((wa[i] + wb[i] + cv[i]) % p for i in rng2))
                    if _linear_form_holds(hyp, op, I, (0, 0), Z) and not _linear_form_holds(goal, op, I, (0, 0), Z):
                        n = p * p
                        elem = lambda k: (k // p, k % p)
                        table = [[(lambda w: w[0] * p + w[1])(tuple((matvec(A, elem(i))[t] + matvec(B, elem(j))[t] + cv[t]) % p
                                                                     for t in rng2)) for j in range(n)] for i in range(n)]
                        return Countermodel(n, table)
    return None


def linear_countermodel(hyp: Equation, goal: Equation, *, n_max: int = 32, primes=(2, 3),
                        time_budget: float = 30.0, table_cap: int | None = None) -> Countermodel | None:
    """Symbolic linear ladder; every hit is re-verified numerically.
    ``table_cap`` (judge style) limits non-affine tables to certifiable
    sizes; affine models have a closed form and may exceed it."""
    deadline = time.monotonic() + time_budget
    if table_cap is not None:
        primes = tuple(p for p in primes if p * p <= table_cap)
    for hit in (_affine_sweep(hyp, goal, n_max, deadline), _matrix_linear_sweep(hyp, goal, primes, deadline)):
        if hit is None:
            continue
        if table_cap is not None and hit.n > table_cap and hit.affine_form() is None:
            continue
        if is_countermodel(hyp, goal, hit.n, hit.table):
            return hit
    return None


# ── 3. structured families ───────────────────────────────────────────────

def structured_tables(n: int) -> Iterator[Table]:
    """A deterministic zoo of structured n×n tables."""
    for c in range(n):
        yield [[c] * n for _ in range(n)]
    yield [[i] * n for i in range(n)]
    yield [list(range(n)) for _ in range(n)]
    yield [[(i + j) % n for j in range(n)] for i in range(n)]
    yield [[(i - j) % n for j in range(n)] for i in range(n)]
    yield [[(j - i) % n for j in range(n)] for i in range(n)]
    yield [[max(i, j) for j in range(n)] for i in range(n)]
    yield [[min(i, j) for j in range(n)] for i in range(n)]
    for k in range(1, n):
        yield [[(i + k) % n for _ in range(n)] for i in range(n)]
        yield [[(j + k) % n for j in range(n)] for _ in range(n)]
    for a in range(n):
        for b in range(n):
            for c in range(n):
                if a == 0 and b == 0:
                    continue
                yield [[(a * i + b * j + c) % n for j in range(n)] for i in range(n)]
    for r in range(n):
        for c in range(n):
            for v in range(1, n):
                t = [[0] * n for _ in range(n)]
                t[r][c] = v
                yield t
    if n <= 5:
        cells = [(r, c) for r in range(n) for c in range(n)]
        for i1 in range(len(cells)):
            for i2 in range(i1 + 1, len(cells)):
                (r1, c1), (r2, c2) = cells[i1], cells[i2]
                for v1 in range(1, n):
                    for v2 in range(1, n):
                        t = [[0] * n for _ in range(n)]
                        t[r1][c1] = v1; t[r2][c2] = v2
                        yield t


# ── 4. complete cell search ──────────────────────────────────────────────

_LEAF, _NODE = 0, 1


def _flatten(t: Term, env, nodes) -> int:
    if isinstance(t, str):
        nodes.append((_LEAF, env[t]))
    else:
        li = _flatten(t[0], env, nodes)
        ri = _flatten(t[1], env, nodes)
        nodes.append((_NODE, li, ri))
    return len(nodes) - 1


def _instances(eq: Equation, n: int):
    """Every ground instance on Fin n as a flat post-order node list."""
    out = []
    vs = list(eq.variables)
    for enc in range(n ** len(vs)):
        env, rem = {}, enc
        for v in vs:
            env[v] = rem % n; rem //= n
        nodes = []
        li = _flatten(eq.lhs, env, nodes)
        ri = _flatten(eq.rhs, env, nodes)
        out.append((nodes, li, ri))
    return out


def _eval_ground(nodes, root, table, n):
    """(value, blocked_cell, at_root) against a partial table."""
    vals = [None] * len(nodes)
    for i, nd in enumerate(nodes):
        if nd[0] == _LEAF:
            vals[i] = nd[1]
            continue
        a, b = vals[nd[1]], vals[nd[2]]
        if a is None or b is None:
            continue
        cell = a * n + b
        v = table[cell]
        if v is None:
            return None, cell, i == root
        vals[i] = v
    return vals[root], None, False


def find_model_cells(hyp: Equation, goal: Equation, n: int, deadline: float):
    """Complete search of Fin n by cell assignment with watched instances,
    unit propagation and the Least Number Heuristic.

    Returns (table | None, exhausted): ``exhausted=True`` is a proof that
    no Fin-n countermodel exists; ``False`` only that the deadline ran out.
    """
    cons, goal_inst = _instances(hyp, n), _instances(goal, n)
    nc = n * n
    table = [None] * nc
    watch = [[] for _ in range(nc)]
    trail = []
    steps = [0]

    def check(ci):
        nodes, li, ri = cons[ci]
        lv, lcell, lroot = _eval_ground(nodes, li, table, n)
        rv, rcell, rroot = _eval_ground(nodes, ri, table, n)
        if lv is not None and rv is not None:
            return lv == rv
        if lv is not None and rroot:
            return assign(rcell, lv)
        if rv is not None and lroot:
            return assign(lcell, rv)
        watch[lcell if lcell is not None else rcell].append(ci)
        return True

    def assign(cell, value):
        cur = table[cell]
        if cur is not None:
            return cur == value
        table[cell] = value
        trail.append(cell)
        pending, watch[cell] = watch[cell], []
        return all(check(ci) for ci in pending)

    def goal_fails():
        for nodes, li, ri in goal_inst:
            lv, _, _ = _eval_ground(nodes, li, table, n)
            rv, _, _ = _eval_ground(nodes, ri, table, n)
            if lv is None or rv is None:
                return False
            if lv != rv:
                return True
        return False

    def branch(cell):
        steps[0] += 1
        if (steps[0] & 0xFF) == 0 and time.monotonic() > deadline:
            return None, False
        while cell < nc and table[cell] is not None:
            cell += 1
        if cell == nc:
            if goal_fails():
                return [table[i * n:(i + 1) * n] for i in range(n)], False
            return None, True
        mx = max((v for v in table[:cell] if v is not None), default=-1)
        exhausted = True
        for v in range(min(n, mx + 2)):
            mark = len(trail)
            saved = [w[:] for w in watch]
            if assign(cell, v):
                found, done = branch(cell + 1)
                if found is not None:
                    return found, False
                if not done:
                    exhausted = False
            while len(trail) > mark:
                table[trail.pop()] = None
            watch[:] = saved
            if not exhausted:
                return None, False
        return None, exhausted

    for ci in range(len(cons)):
        if not check(ci):
            return None, True
    return branch(0)


# ── 5. CDCL ──────────────────────────────────────────────────────────────

class SatSolver:
    """A compact CDCL solver: two watched literals, 1UIP learning,
    activity-based branching with phase saving, geometric restarts."""

    def __init__(self, nvars: int):
        self.nv = nvars
        self.clauses: list[list[int]] = []
        self.watch = [[] for _ in range(2 * nvars + 2)]
        self.val = [0] * (nvars + 1)
        self.level = [0] * (nvars + 1)
        self.reason = [-1] * (nvars + 1)
        self.trail: list[int] = []
        self.lim: list[int] = []
        self.act = [0.0] * (nvars + 1)
        self.bump = 1.0
        self.phase = [False] * (nvars + 1)
        self.ok = True
        self.qhead = 0

    def _wi(self, lit):
        return 2 * abs(lit) + (0 if lit > 0 else 1)

    def value(self, lit):
        a = self.val[abs(lit)]
        return 0 if a == 0 else (a if lit > 0 else -a)

    def add(self, lits):
        if not self.ok:
            return
        seen, out = set(), []
        for l in lits:
            if -l in seen:
                return
            if l not in seen:
                seen.add(l); out.append(l)
        if not out:
            self.ok = False
            return
        if len(out) == 1:
            if self.value(out[0]) < 0:
                self.ok = False
            elif self.value(out[0]) == 0:
                self._enqueue(out[0], -1)
            return
        ci = len(self.clauses)
        self.clauses.append(out)
        self.watch[self._wi(out[0])].append(ci)
        self.watch[self._wi(out[1])].append(ci)

    def _enqueue(self, lit, reason):
        v = abs(lit)
        self.val[v] = 1 if lit > 0 else -1
        self.level[v] = len(self.lim)
        self.reason[v] = reason
        self.trail.append(lit)

    def _propagate(self):
        while self.qhead < len(self.trail):
            lit = self.trail[self.qhead]
            self.qhead += 1
            wi = self._wi(-lit)
            watchers, self.watch[wi] = self.watch[wi], []
            for k, ci in enumerate(watchers):
                c = self.clauses[ci]
                if c[0] == -lit:
                    c[0], c[1] = c[1], c[0]
                if self.value(c[0]) > 0:
                    self.watch[wi].append(ci)
                    continue
                for i in range(2, len(c)):
                    if self.value(c[i]) >= 0:
                        c[1], c[i] = c[i], c[1]
                        self.watch[self._wi(c[1])].append(ci)
                        break
                else:
                    self.watch[wi].append(ci)
                    if self.value(c[0]) < 0:
                        self.watch[wi].extend(watchers[k + 1:])
                        self.qhead = len(self.trail)
                        return ci
                    self._enqueue(c[0], ci)
        return -1

    def _analyze(self, conflict):
        lvl = len(self.lim)
        seen, learnt, counter, p, idx, ci = set(), [0], 0, 0, len(self.trail) - 1, conflict
        while True:
            for q in self.clauses[ci]:
                v = abs(q)
                if v in seen or self.level[v] == 0 or q == p:
                    continue
                seen.add(v)
                self.act[v] += self.bump
                if self.level[v] >= lvl:
                    counter += 1
                else:
                    learnt.append(q)
            while True:
                p = self.trail[idx]; idx -= 1
                if abs(p) in seen:
                    break
            seen.discard(abs(p))
            counter -= 1
            if counter <= 0:
                break
            ci = self.reason[abs(p)]
        learnt[0] = -p
        if len(learnt) == 1:
            return learnt, 0
        best = max(range(1, len(learnt)), key=lambda i: self.level[abs(learnt[i])])
        learnt[1], learnt[best] = learnt[best], learnt[1]
        return learnt, self.level[abs(learnt[1])]

    def _backtrack(self, lvl):
        if len(self.lim) <= lvl:
            return
        start = self.lim[lvl]
        for lit in self.trail[start:]:
            v = abs(lit)
            self.phase[v] = lit > 0
            self.val[v] = 0
            self.reason[v] = -1
        del self.trail[start:]
        del self.lim[lvl:]
        self.qhead = len(self.trail)

    def _pick(self):
        best, ba = 0, -1.0
        for v in range(1, self.nv + 1):
            if self.val[v] == 0 and self.act[v] > ba:
                best, ba = v, self.act[v]
        if best == 0:
            return 0
        return best if self.phase[best] else -best

    def solve(self, deadline: float):
        """A model (list of true literals), False for UNSAT, None on timeout."""
        if not self.ok:
            return False
        conflicts, limit, checks = 0, 100, 0
        while True:
            ci = self._propagate()
            if ci >= 0:
                if not self.lim:
                    return False
                conflicts += 1
                learnt, lvl = self._analyze(ci)
                self._backtrack(lvl)
                if len(learnt) == 1:
                    if self.value(learnt[0]) < 0:
                        return False
                    if self.value(learnt[0]) == 0:
                        self._enqueue(learnt[0], -1)
                else:
                    k = len(self.clauses)
                    self.clauses.append(learnt)
                    self.watch[self._wi(learnt[0])].append(k)
                    self.watch[self._wi(learnt[1])].append(k)
                    self._enqueue(learnt[0], k)
                self.bump *= 1.02
                if self.bump > 1e30:
                    self.act = [a * 1e-30 for a in self.act]
                    self.bump *= 1e-30
                if conflicts >= limit:
                    conflicts, limit = 0, int(limit * 1.5)
                    self._backtrack(0)
                continue
            checks += 1
            if (checks & 0x3FF) == 0 and time.monotonic() > deadline:
                return None
            lit = self._pick()
            if lit == 0:
                return [v if self.val[v] > 0 else -v for v in range(1, self.nv + 1)]
            self.lim.append(len(self.trail))
            self._enqueue(lit, -1)


class _Encoder:
    """Slots are ("c", cell_var_base) for a known cell or ("b", block_base)
    for a one-hot block of n value variables."""

    def __init__(self, n):
        self.n = n
        self.next = n * n * n + 1
        self.cl: list[list[int]] = []

    def cell(self, i, j, v):
        return 1 + (i * self.n + j) * self.n + v

    def block(self):
        base = self.next
        self.next += self.n
        return base

    def amo(self, base):
        for a in range(self.n):
            for b in range(a + 1, self.n):
                self.cl.append([-(base + a), -(base + b)])

    def node(self, ls, rs):
        n = self.n
        if ls[0] == "c" and rs[0] == "c":
            return ("b", self.cell(ls[1], rs[1], 0))
        y = self.block()
        self.amo(y)
        if ls[0] == "c":
            a = ls[1]
            for b in range(n):
                for v in range(n):
                    self.cl.append([-(rs[1] + b), -self.cell(a, b, v), y + v])
        elif rs[0] == "c":
            b = rs[1]
            for a in range(n):
                for v in range(n):
                    self.cl.append([-(ls[1] + a), -self.cell(a, b, v), y + v])
        else:
            for a in range(n):
                for b in range(n):
                    for v in range(n):
                        self.cl.append([-(ls[1] + a), -(rs[1] + b), -self.cell(a, b, v), y + v])
        return ("b", y)

    def term(self, t, env):
        if isinstance(t, str):
            return ("c", env[t])
        return self.node(self.term(t[0], env), self.term(t[1], env))

    def equal(self, s1, s2):
        if s1[0] == "c" and s2[0] == "c":
            if s1[1] != s2[1]:
                self.cl.append([])
            return
        if s1[0] == "c":
            s1, s2 = s2, s1
        if s2[0] == "c":
            self.cl.append([s1[1] + s2[1]])
            return
        for v in range(self.n):
            self.cl.append([-(s1[1] + v), s2[1] + v])
            self.cl.append([-(s2[1] + v), s1[1] + v])

    def differ(self, s1, s2, sel):
        if s1[0] == "c" and s2[0] == "c":
            if s1[1] == s2[1]:
                self.cl.append([-sel])
            return
        if s1[0] == "c":
            s1, s2 = s2, s1
        if s2[0] == "c":
            self.cl.append([-sel, -(s1[1] + s2[1])])
            return
        for v in range(self.n):
            self.cl.append([-sel, -(s1[1] + v), -(s2[1] + v)])


def _assignments(eq: Equation, n: int):
    vs = list(eq.variables)
    for code in range(n ** len(vs)):
        env, rem = {}, code
        for v in vs:
            env[v] = rem % n; rem //= n
        yield env


def sat_encode(hyp: Equation, goal: Equation, n: int):
    """CNF for "some magma on Fin n satisfies hyp and refutes goal", with
    a value-symmetry ladder (a value may only appear after its
    predecessor has) that removes the n! renamings of every model."""
    enc = _Encoder(n)
    cl = enc.cl
    for i in range(n):
        for j in range(n):
            cl.append([enc.cell(i, j, v) for v in range(n)])
            enc.amo(enc.cell(i, j, 0))
    prev = enc.block()
    for v in range(n):
        cl.append([-(prev + v)])
    for k in range(n * n):
        ci, cj = divmod(k, n)
        nxt = enc.block()
        for v in range(n):
            ck = enc.cell(ci, cj, v)
            if v >= 1:
                cl.append([-ck, prev + (v - 1)])
            cl.append([-(prev + v), nxt + v])
            cl.append([-ck, nxt + v])
            cl.append([-(nxt + v), prev + v, ck])
        prev = nxt
    for env in _assignments(hyp, n):
        enc.equal(enc.term(hyp.lhs, env), enc.term(hyp.rhs, env))
    selectors = []
    for env in _assignments(goal, n):
        s = enc.next
        enc.next += 1
        selectors.append(s)
        enc.differ(enc.term(goal.lhs, env), enc.term(goal.rhs, env), s)
    cl.append(selectors)
    return enc.next - 1, cl


def _node_costs(t, costs):
    if isinstance(t, str):
        return True
    left, right = _node_costs(t[0], costs), _node_costs(t[1], costs)
    if left and right:
        return False
    costs.append(2 if (left or right) else 3)
    return False


def sat_clause_estimate(hyp: Equation, goal: Equation, n: int) -> int:
    """Clause-count estimate for the memory budget, computed before
    allocating (the at-most-one clauses of computed subterms are not
    counted, so it can undershoot by a small factor)."""
    total = n * n * (1 + n * (n - 1) // 2) + n * n * 4 * n
    for eq, extra in ((hyp, 2), (goal, 1)):
        costs = []
        _node_costs(eq.lhs, costs); _node_costs(eq.rhs, costs)
        total += (n ** len(eq.variables)) * (sum(n ** c for c in costs) + extra * n)
    return total


SAT_BYTES_PER_CLAUSE = 480       # measured peak, learnt clauses included


def find_model_sat(hyp: Equation, goal: Equation, n: int, deadline: float):
    """Complete Fin-n search via CDCL. Same contract as :func:`find_model_cells`."""
    nv, clauses = sat_encode(hyp, goal, n)
    s = SatSolver(nv)
    for c in clauses:
        s.add(c)
    del clauses
    res = s.solve(deadline)
    if res is None:
        return None, False
    if res is False:
        return None, True
    true = {l for l in res if l > 0}
    table = [[next(v for v in range(n) if (1 + (i * n + j) * n + v) in true) for j in range(n)] for i in range(n)]
    return table, False


def decide_size(hyp: Equation, goal: Equation, n: int, deadline: float, memory_mb: float | None = None):
    """Decide Fin n: (table, exhausted). CDCL when its encoding fits in
    ``memory_mb`` (60 % share), the cell search otherwise — both complete,
    so the verdict does not depend on which one ran."""
    memory_mb = settings.sat_memory_mb if memory_mb is None else memory_mb
    cap = int(memory_mb * 0.6 * 1024 * 1024 / SAT_BYTES_PER_CLAUSE)
    if sat_clause_estimate(hyp, goal, n) <= cap:
        try:
            return find_model_sat(hyp, goal, n, deadline)
        except (MemoryError, RecursionError):
            pass
    return find_model_cells(hyp, goal, n, deadline)


# ── the ladder ───────────────────────────────────────────────────────────

EARLY_SIZES = (4, 5)
EARLY_SHARE, EARLY_FLOOR = 0.10, 5.0


def find_countermodel(hyp: Equation, goal: Equation, *, time_budget: float = 30.0, max_n: int | None = None,
                      facts: SearchFacts | None = None, memory_mb: float | None = None) -> Countermodel | None:
    """The full ladder: symbolic linear → capped complete search on the
    early sizes → structured/affine → bilinear → seeded random → complete
    search on every size still open, up to ``max_n``.

    A verified countermodel or None; ``facts`` collects exhaustion verdicts.
    """
    facts = facts if facts is not None else SearchFacts()
    max_n = settings.model_max_n if max_n is None else max_n
    start = time.monotonic()
    deadline = start + time_budget

    def backtrack(n, until):
        table, done = decide_size(hyp, goal, n, until, memory_mb)
        if done and n not in facts.exhausted:
            facts.exhausted.append(n)
        return table

    hit = linear_countermodel(hyp, goal, time_budget=max(0.0, deadline - time.monotonic()))
    if hit is not None:
        return hit

    early_cap = min(deadline, time.monotonic() + max(EARLY_FLOOR, time_budget * EARLY_SHARE))
    for n in EARLY_SIZES:
        if n > max_n:
            break
        table = backtrack(n, early_cap)
        if table is not None:
            return Countermodel(n, table)
        if time.monotonic() > early_cap:
            break

    for n in range(4, min(8, max_n) + 1):
        if n in facts.exhausted:
            continue
        for checked, table in enumerate(structured_tables(n)):
            if is_countermodel(hyp, goal, n, table):
                return Countermodel(n, table)
            if (checked & 0xFF) == 0 and time.monotonic() > deadline:
                return None
        if n not in facts.searched:
            facts.searched.append(n)

    for n in (4, 5):
        if n in facts.exhausted or n > max_n:
            continue
        for a in range(n):
            for b in range(n):
                for c in range(1, n):
                    for d in range(n):
                        table = [[(a * i + b * j + c * i * j + d) % n for j in range(n)] for i in range(n)]
                        if is_countermodel(hyp, goal, n, table):
                            return Countermodel(n, table)
                if time.monotonic() > deadline:
                    return None

    for n, attempts in ((4, 30000), (5, 20000), (6, 8000)):
        if n in facts.exhausted or n > max_n:
            continue
        rng = random.Random(n)
        for i in range(attempts):
            table = [[rng.randint(0, n - 1) for _ in range(n)] for _ in range(n)]
            if is_countermodel(hyp, goal, n, table):
                return Countermodel(n, table)
            if (i & 0xFF) == 0 and time.monotonic() > deadline:
                return None

    for n in range(4, max_n + 1):
        if n in facts.exhausted:
            continue
        table = backtrack(n, deadline)
        if table is not None:
            return Countermodel(n, table)
        if time.monotonic() > deadline:
            return None
    return None
