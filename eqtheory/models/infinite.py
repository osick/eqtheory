"""Infinite countermodels on ℕ for *Austin pairs* — implications that
hold in every finite magma but fail in some infinite one, so no table
search at any order can answer them.

The family searched is residue-class affine (a "PORC"-style recipe):

    op(x, y) = A[r][s]·x + B[r][s]·y + C[r][s]   (truncated at 0),
    r = x mod m,  s = y mod m,  m ∈ {2, 3}.

Translation-like configurations (A = 0, B = 1) are enumerated first —
they are what the Equational Theories Project's infinite-model
constructions predict. The numeric check on small ranges is only
*necessary* evidence; :func:`eqtheory.lean.false_nat_residue_code` emits
the certificate whose law is verified by Lean's ``grind``.
"""
from __future__ import annotations

import itertools
import time
from dataclasses import dataclass

from ..terms import Equation, evaluate


@dataclass(frozen=True)
class NatResidueModel:
    m: int
    A: list
    B: list
    C: list
    witness: tuple

    def op(self, x: int, y: int) -> int:
        r, s = x % self.m, y % self.m
        return max(self.A[r][s] * x + self.B[r][s] * y + self.C[r][s], 0)


def _configs(m: int, deadline: float):
    classes = [(r, s) for r in range(m) for s in range(m)]
    k = len(classes)
    if m == 2:
        coef_order = ((0, 1), (1, 0), (0, 2), (1, 1), (2, 0), (0, 0))
        for ab in itertools.product(coef_order, repeat=k):
            if time.monotonic() >= deadline:
                return
            for cs in itertools.product((1, -1, 0, 2, -2), repeat=k):
                A = [[0] * m for _ in range(m)]; B = [[0] * m for _ in range(m)]; C = [[0] * m for _ in range(m)]
                for (r, s), (a, b), c in zip(classes, ab, cs):
                    A[r][s] = a; B[r][s] = b; C[r][s] = c
                yield A, B, C
    else:
        for ga, gb in ((0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (0, 0)):
            if time.monotonic() >= deadline:
                return
            for cs in itertools.product((1, -1, 0), repeat=k):
                A = [[ga] * m for _ in range(m)]; B = [[gb] * m for _ in range(m)]; C = [[0] * m for _ in range(m)]
                for (r, s), c in zip(classes, cs):
                    C[r][s] = c
                yield A, B, C


def _holds_on(eq: Equation, op, sample) -> bool:
    for vals in itertools.product(sample, repeat=len(eq.variables)):
        env = dict(zip(eq.variables, vals))
        if evaluate(eq.lhs, op, env) != evaluate(eq.rhs, op, env):
            return False
    return True


def _witness(eq: Equation, op, sample):
    for vals in itertools.product(sample, repeat=len(eq.variables)):
        env = dict(zip(eq.variables, vals))
        if evaluate(eq.lhs, op, env) != evaluate(eq.rhs, op, env):
            return vals
    return None


def residue_affine_countermodel(hyp: Equation, goal: Equation, *, time_budget: float = 30.0,
                                m_values=(2, 3)) -> NatResidueModel | None:
    """Search the residue-class affine ℕ family. Purely at runtime: the
    family is enumerated and checked against *these* two equations."""
    if not hyp.variables or not goal.variables:
        return None
    deadline = time.monotonic() + time_budget
    for m in m_values:
        hyp_small, goal_small = range(0, 2 * m + 3), range(0, m + 3)
        for A, B, C in _configs(m, deadline):
            cand = NatResidueModel(m, A, B, C, ())
            if not _holds_on(hyp, cand.op, hyp_small):
                continue
            w = _witness(goal, cand.op, goal_small)
            if w is None:
                continue
            if _holds_on(hyp, cand.op, (0, 1, 2, 5, 12, 25)):
                return NatResidueModel(m, A, B, C, tuple(w))
    return None
