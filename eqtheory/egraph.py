"""A hash-consed e-graph with congruence closure and a proof forest, and
equality saturation of an equational hypothesis over a term universe.

The e-graph is the classic structure (Nelson–Oppen congruence closure,
egg-style rebuilding) with one addition that the certificate requirement
forces: every union records a *proof-forest edge* with a reason, so any
two equal terms can later be explained by a chain of literal hypothesis
instances and congruence steps (:mod:`eqtheory.proofs`). Explanations are
extracted as a *shared* DAG — each distinct explained node pair becomes a
named sub-proof — because inlining them re-explains the same pairs
exponentially often.

Saturation (:func:`saturate`) instantiates the hypothesis (and any derived
lemma rules) over small class representatives, unions the two instance
nodes, and rebuilds congruence; a second "collapse" pass e-matches each
rule's larger side against existing nodes and instantiates the found
substitutions literally. It stops as soon as the two goal terms share a
class, or when its instantiation/node budgets run out.
"""
from __future__ import annotations

import heapq
import itertools
import time
from typing import Iterator, Mapping, Sequence

from .proofs import Chain, invert
from .terms import Equation, Term, term_leaves

Reason = tuple


class EGraph:
    """Nodes are ints; ``nodes[i]`` is ``('var', name)`` or
    ``('op', l, r)`` with child ids fixed at creation, so every node
    denotes one concrete term (:meth:`term_of`). Classes live in a
    union-find; ``cong`` maps ``(find(l), find(r))`` to a representative
    op node and :meth:`rebuild` restores congruence after unions.

    Every union records a proof-forest edge ``(neighbour, reason, ts)``.
    Reasons: ``('r', rule_name, arg_node_ids, lhs_instance_node)`` for a
    rule instance, ``('cong',)`` for congruence.
    """

    def __init__(self, extra_edge_cap: int = 400_000):
        self.nodes: list = []
        self.parent: list[int] = []
        self.size: list[int] = []        # min leaf count within the class
        self.cong: dict = {}
        self.uses: dict = {}
        self.memo_var: dict = {}
        self.memo_op: dict = {}
        self._worklist: list[int] = []
        self.pf_edge: dict = {}
        self.union_ts = 0
        self.extra_edges: list = []      # redundant unions = shortcut edges
        self.extra_edge_cap = extra_edge_cap

    # ── construction ──
    def add_var(self, name: str) -> int:
        nid = self.memo_var.get(name)
        if nid is not None:
            return nid
        nid = self._new_node(("var", name), 1)
        self.memo_var[name] = nid
        return nid

    def add_op(self, l: int, r: int) -> int:
        nid = self.memo_op.get((l, r))
        if nid is not None:
            return nid
        nid = self._new_node(("op", l, r), self.size[l] + self.size[r])
        self.memo_op[(l, r)] = nid
        l_rep, r_rep = self.find(l), self.find(r)
        self.uses.setdefault(l_rep, []).append(nid)
        self.uses.setdefault(r_rep, []).append(nid)
        existing = self.cong.get((l_rep, r_rep))
        if existing is None:
            self.cong[(l_rep, r_rep)] = nid
        elif self.find(existing) != self.find(nid):
            self.union(nid, existing, ("cong",))
        return nid

    def add_term(self, term: Term, env: Mapping[str, int] | None = None) -> int:
        """Insert a term; free variables become e-graph variables."""
        if isinstance(term, str):
            if env is not None and term in env:
                return env[term]
            return self.add_var(term)
        return self.add_op(self.add_term(term[0], env), self.add_term(term[1], env))

    def _new_node(self, struct, size) -> int:
        nid = len(self.nodes)
        self.nodes.append(struct)
        self.parent.append(nid)
        self.size.append(size)
        return nid

    # ── union-find ──
    def find(self, x: int) -> int:
        root = x
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[x] != root:
            self.parent[x], x = root, self.parent[x]
        return root

    def equal(self, u: int, v: int) -> bool:
        return self.find(u) == self.find(v)

    def union(self, u: int, v: int, reason: Reason) -> bool:
        self.union_ts += 1
        ru, rv = self.find(u), self.find(v)
        if ru == rv:
            if u != v and len(self.extra_edges) < self.extra_edge_cap:
                self.extra_edges.append((u, v, reason, self.union_ts))
            return False
        if self.size[rv] < self.size[ru]:
            ru, rv = rv, ru
        self.parent[rv] = ru
        self.size[ru] = min(self.size[ru], self.size[rv])
        for n in self.uses.pop(rv, []):
            self.uses.setdefault(ru, []).append(n)
            self._worklist.append(n)
        self._pf_reroot(u)
        self.pf_edge[u] = (v, reason, self.union_ts)
        return True

    def _pf_reroot(self, u: int) -> None:
        prev, prev_edge, cur = None, None, u
        while cur is not None:
            nxt = self.pf_edge.get(cur)
            if prev is not None:
                self.pf_edge[cur] = (prev, prev_edge[1], prev_edge[2])
            elif cur in self.pf_edge:
                del self.pf_edge[cur]
            prev, prev_edge = cur, nxt
            cur = nxt[0] if nxt is not None else None

    def rebuild(self) -> None:
        while self._worklist:
            n = self._worklist.pop()
            struct = self.nodes[n]
            if struct[0] != "op":
                continue
            key = (self.find(struct[1]), self.find(struct[2]))
            existing = self.cong.get(key)
            if existing is None:
                self.cong[key] = n
            elif self.find(existing) != self.find(n):
                self.union(existing, n, ("cong",))

    # ── inspection ──
    def term_of(self, nid: int) -> Term:
        struct = self.nodes[nid]
        if struct[0] == "var":
            return struct[1]
        return (self.term_of(struct[1]), self.term_of(struct[2]))

    def classes(self) -> dict[int, list[int]]:
        """Representative → member node ids."""
        out: dict[int, list[int]] = {}
        for i in range(len(self.nodes)):
            out.setdefault(self.find(i), []).append(i)
        return out

    def __len__(self) -> int:
        return len(self.nodes)

    # ── e-matching ──
    def ematch(self, pattern: Term, nid: int, sub: dict | None = None) -> Iterator[dict]:
        """Match ``pattern`` against node ``nid`` modulo congruence; pattern
        variables bind class representatives."""
        if sub is None:
            sub = {}
        if isinstance(pattern, str):
            rep = self.find(nid)
            bound = sub.get(pattern)
            if bound is None:
                s2 = dict(sub)
                s2[pattern] = rep
                yield s2
            elif self.find(bound) == rep:
                yield sub
            return
        struct = self.nodes[nid]
        if struct[0] != "op":
            return
        for s1 in self.ematch(pattern[0], struct[1], sub):
            yield from self.ematch(pattern[1], struct[2], s1)

    # ── explanation ──
    def explain(self, u: int, v: int) -> tuple[list, Chain] | None:
        """Shared proof of ``term_of(u) = term_of(v)``: (lemmas, chain), or
        ``None`` if the nodes are not connected."""
        b = _ProofBuilder(self)
        try:
            chain = b.chain(u, v)
        except (ExtractionError, RecursionError):
            return None
        return b.lemmas, chain

    # ── visualisation ──
    def to_dot(self, highlight: Sequence[int] = (), proof_pairs: Sequence[tuple[int, int]] = ()) -> str:
        from .viz import egraph_to_dot
        return egraph_to_dot(self, highlight=highlight, proof_pairs=proof_pairs)

    def render(self, path: str, highlight: Sequence[int] = (), proof_pairs: Sequence[tuple[int, int]] = ()) -> str:
        from .viz import render_egraph
        return render_egraph(self, path, highlight=highlight, proof_pairs=proof_pairs)


class ExtractionError(Exception):
    pass


class _ProofBuilder:
    """Shared-proof extraction over forest + shortcut edges: weighted
    shortest path (rule edges cheap, congruence edges expensive), with
    congruence edges explained recursively via strictly older edges."""
    _INF = float("inf")
    _CONG_WEIGHT = 32

    def __init__(self, eg: EGraph):
        self.eg = eg
        self.lemmas: list = []
        self.memo: dict = {}
        self.active: set = set()
        self.adj: dict = {}
        for x, (y, reason, ts) in eg.pf_edge.items():
            self.adj.setdefault(x, []).append((y, x, y, reason, ts))
            self.adj.setdefault(y, []).append((x, x, y, reason, ts))
        for x, y, reason, ts in eg.extra_edges:
            self.adj.setdefault(x, []).append((y, x, y, reason, ts))
            self.adj.setdefault(y, []).append((x, x, y, reason, ts))

    def chain(self, u: int, v: int, bound=None) -> Chain:
        if u == v:
            return []
        if bound is None:
            bound = self._INF
        prev: dict = {}
        dist = {u: 0}
        heap = [(0, u)]
        while heap:
            d, cur = heapq.heappop(heap)
            if cur == v:
                break
            if d > dist.get(cur, self._INF):
                continue
            for (other, ex, ey, reason, ts) in self.adj.get(cur, ()):
                if ts >= bound:
                    continue
                nd = d + (1 if reason[0] == "r" else self._CONG_WEIGHT)
                if nd < dist.get(other, self._INF):
                    dist[other] = nd
                    prev[other] = (cur, ex, ey, reason, ts)
                    heapq.heappush(heap, (nd, other))
        if v not in prev:
            raise ExtractionError("nodes not connected under bound")
        steps = []
        cur = v
        while cur != u:
            parent, ex, ey, reason, ts = prev[cur]
            steps.append((parent, ex, ey, reason, ts))
            cur = parent
        steps.reverse()
        chain: Chain = []
        for frm, ex, ey, reason, ts in steps:
            links = self._edge_links(ex, ey, reason, ts)
            if frm != ex:
                links = invert(links)
            chain.extend(links)
        return chain

    def ref(self, u: int, v: int, bound) -> Chain:
        if u == v:
            return []
        lo, hi = (u, v) if u < v else (v, u)
        name = self.memo.get((lo, hi))
        if name is None:
            if (lo, hi) in self.active:
                return self.chain(u, v, bound)
            self.active.add((lo, hi))
            try:
                sub = self.chain(lo, hi, bound)
            finally:
                self.active.discard((lo, hi))
            name = f"e{len(self.lemmas) + 1}"
            self.lemmas.append((name, self.eg.term_of(lo), self.eg.term_of(hi), sub))
            self.memo[(lo, hi)] = name
        return [("ref", name, u != lo)]

    def _edge_links(self, x: int, y: int, reason, ts) -> Chain:
        if reason[0] == "r":
            _, rname, combo, lhs_node = reason
            sigma = tuple(self.eg.term_of(n) for n in combo)
            if rname == "h":
                return [("h", sigma, x == lhs_node)]
            return [("lem", rname, sigma, x == lhs_node)]
        sx, sy = self.eg.nodes[x], self.eg.nodes[y]
        left = self.ref(sx[1], sy[1], ts)
        right = self.ref(sx[2], sy[2], ts)
        if not left and not right:
            return []
        return [("cong", left, right)]


# ── equality saturation ──────────────────────────────────────────────────

def saturate(hypothesis: Equation, consts: Sequence[str], goal: tuple[Term, Term], *,
             lemmas: Sequence[dict] = (), max_rounds: int = 8, time_budget: float = 25.0,
             node_cap: int = 1_200_000, inst_cap: int = 300_000, pool_size_cap: int = 5,
             egraph: EGraph | None = None) -> tuple[EGraph, int, int, bool]:
    """Equality-saturate instances of ``hypothesis`` (plus ``lemmas``, each a
    dict with ``name``, ``lhs``, ``rhs``, ``vars``) over the universe of
    terms in the constants ``consts``; stop when the two ``goal`` terms
    (over ``consts``) share a class.

    Returns ``(egraph, goal_lhs_id, goal_rhs_id, merged)``.
    """
    rules = [("h", hypothesis.lhs, hypothesis.rhs, tuple(hypothesis.variables))]
    for lem in lemmas:
        rules.append((lem["name"], lem["lhs"], lem["rhs"], tuple(lem["vars"])))
    eg = egraph or EGraph()
    env = {c: eg.add_var(c) for c in consts}
    leaves = [env[c] for c in consts]
    two = [eg.add_op(x, y) for x in leaves for y in leaves]
    for t in two:
        for c in leaves:
            eg.add_op(t, c)
            eg.add_op(c, t)
    l_id = eg.add_term(goal[0], env)
    r_id = eg.add_term(goal[1], env)
    if eg.equal(l_id, r_id):
        return eg, l_id, r_id, True
    deadline = time.monotonic() + time_budget
    for _ in range(max_rounds):
        changed = False
        reps = sorted({eg.find(i) for i in range(len(eg.nodes))})
        pool = sorted((r for r in reps if eg.size[r] <= pool_size_cap), key=lambda r: (eg.size[r], r))
        n_inst, out_of_budget = 0, False
        for (rname, LL, RR, rvars) in rules:
            stop_rule = False
            for combo in itertools.product(pool, repeat=len(rvars)):
                sub = dict(zip(rvars, combo))
                li = eg.add_term(LL, sub)
                ri = eg.add_term(RR, sub)
                if eg.union(li, ri, ("r", rname, tuple(combo), li)):
                    changed = True
                eg.rebuild()
                n_inst += 1
                if n_inst % 1024 == 0:
                    if eg.equal(l_id, r_id):
                        return eg, l_id, r_id, True
                    if time.monotonic() > deadline or len(eg.nodes) > node_cap:
                        out_of_budget = True
                        break
                    if n_inst >= inst_cap:
                        stop_rule = True
                        break
            if out_of_budget or stop_rule:
                break
        eg.rebuild()
        if eg.equal(l_id, r_id):
            return eg, l_id, r_id, True
        if out_of_budget:
            break
        for (rname, LL, RR, rvars) in rules:
            big = RR if term_leaves(RR) >= term_leaves(LL) else LL
            for nid in range(len(eg.nodes)):
                if eg.nodes[nid][0] != "op":
                    continue
                for sub in eg.ematch(big, nid):
                    if any(v not in sub for v in rvars):
                        continue
                    li = eg.add_term(LL, sub)
                    ri = eg.add_term(RR, sub)
                    if eg.union(li, ri, ("r", rname, tuple(sub[v] for v in rvars), li)):
                        changed = True
                    eg.rebuild()
                if nid % 4096 == 0 and (time.monotonic() > deadline or len(eg.nodes) > node_cap):
                    break
            if time.monotonic() > deadline or len(eg.nodes) > node_cap:
                break
        if eg.equal(l_id, r_id):
            return eg, l_id, r_id, True
        if not changed or time.monotonic() > deadline:
            break
    return eg, l_id, r_id, eg.equal(l_id, r_id)


def prove_goal(hypothesis: Equation, goal: Equation, **kw) -> tuple[EGraph, int, int] | None:
    """Connect the goal's two sides by hypothesis instances over the goal's
    variables. Returns ``(egraph, lhs_id, rhs_id)`` or ``None``."""
    if not goal.variables:
        return None
    eg, l, r, ok = saturate(hypothesis, goal.variables, (goal.lhs, goal.rhs), **kw)
    return (eg, l, r) if ok else None


def prove_singleton(hypothesis: Equation, **kw) -> tuple[EGraph, int, int] | None:
    """Does the hypothesis force ``a = b`` for fresh constants (a singleton
    magma, hence every goal)? Returns ``(egraph, a_id, b_id)`` or ``None``."""
    eg, a, b, ok = saturate(hypothesis, ("a", "b"), ("a", "b"), **kw)
    return (eg, a, b) if ok else None
