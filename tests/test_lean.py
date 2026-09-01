"""Every certificate shape compiled with a real Lean 4 toolchain (skipped
when none is installed). Standalone certificates need no library."""
import time

import pytest

from eqtheory import Problem, prove_by_superposition, prove_goal, solve, Config
from eqtheory.lean import certs, check as lean_check
from eqtheory.models import finite, infinite

CFG = lean_check.configure()
pytestmark = pytest.mark.skipif(CFG is None, reason="no Lean 4 binary found")

EQSAT = Problem.parse("x = x ◇ y", "x = (x ◇ y) ◇ z")
KNOWN_FALSE = Problem.parse("x = (y ◇ x) ◇ (x ◇ z)", "x = y ◇ (x ◇ (y ◇ z))")
ORDER5_A = Problem.parse("x = (y ◇ (z ◇ (z ◇ (x ◇ z)))) ◇ z", "x = (x ◇ y) ◇ (((z ◇ z) ◇ z) ◇ z)")
AUSTIN = Problem.parse("x = y ◇ ((z ◇ (y ◇ y)) ◇ x)", "x = (y ◇ z) ◇ ((x ◇ z) ◇ x)")
IDEM = Problem.parse("x = x", "x = x ◇ x")


def ok(code):
    res = lean_check.compile_certificate(code, CFG)
    assert res.ok, res.output
    return res


def test_egraph_proof():
    eg, l, r = prove_goal(EQSAT.hypothesis, EQSAT.goal, time_budget=5)
    lemmas, chain = eg.explain(l, r)
    ok(certs.egraph_proof_code(EQSAT.hypothesis, EQSAT.goal, lemmas, chain))


def test_superposition_proof_with_lemma_haves():
    pr = prove_by_superposition(ORDER5_A.hypothesis, ORDER5_A.goal)
    ok(certs.superposition_code(ORDER5_A.hypothesis, ORDER5_A.goal, pr))


def test_finite_table_and_affine():
    cm = finite.find_countermodel(KNOWN_FALSE.hypothesis, KNOWN_FALSE.goal, time_budget=60)
    assert cm is not None
    ok(certs.false_table_code(cm.n, cm.table, KNOWN_FALSE.hypothesis, KNOWN_FALSE.goal))
    n, a, b, c = 11, 1, 1, 1
    table = [[(a * i + b * j + c) % n for j in range(n)] for i in range(n)]
    assert finite.is_countermodel(IDEM.hypothesis, IDEM.goal, n, table)
    res = ok(certs.false_code(n, table, IDEM.hypothesis, IDEM.goal))
    assert res.verdict == "false"
    # a table past the old judge ceiling
    n = 12
    table = [[(i * j) % n for j in range(n)] for i in range(n)]
    assert finite.is_countermodel(IDEM.hypothesis, IDEM.goal, n, table)
    ok(certs.false_table_code(n, table, IDEM.hypothesis, IDEM.goal))


def test_nat_residue_model():
    m = infinite.residue_affine_countermodel(AUSTIN.hypothesis, AUSTIN.goal, time_budget=30)
    ok(certs.false_nat_residue_code(AUSTIN.hypothesis, m.m, m.A, m.B, m.C, m.witness, AUSTIN.goal))


def test_pipeline_with_judge():
    t0 = time.monotonic()
    cfg = Config(eqsat_budget=5, superposition_budget=20, model_budget=60)
    ans = solve(KNOWN_FALSE, cfg, judge=lean_check.make_judge(CFG))
    assert ans is not None and ans.verdict == "false" and time.monotonic() - t0 < 200


def test_wrong_certificate_is_rejected():
    code = certs.true_code("intro x y z\nexact (h x y).symm", EQSAT.hypothesis, EQSAT.goal)
    assert not lean_check.compile_certificate(code, CFG).ok
