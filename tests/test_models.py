import time

from eqtheory import Problem
from eqtheory.lean import certs
from eqtheory.models import (SearchFacts, decide_size, find_countermodel, find_model_cells, find_model_sat,
                             is_countermodel, linear_countermodel, residue_affine_countermodel, scan)
from eqtheory.models.finite import sat_encode, sat_clause_estimate

KNOWN_FALSE = Problem.parse("x = (y ◇ x) ◇ (x ◇ z)", "x = y ◇ (x ◇ (y ◇ z))")
ORDER5_A = Problem.parse("x = (y ◇ (z ◇ (z ◇ (x ◇ z)))) ◇ z", "x = (x ◇ y) ◇ (((z ◇ z) ◇ z) ◇ z)")
AUSTIN = Problem.parse("x = y ◇ ((z ◇ (y ◇ y)) ◇ x)", "x = (y ◇ z) ◇ ((x ◇ z) ◇ x)")
TRIVIAL_FALSE = Problem.parse("x = x", "x = y")
COMM_FALSE = Problem.parse("x ◇ y = y ◇ x", "x = x ◇ x")


def test_scan_finds_tiny_countermodels():
    cm, has_model = scan(TRIVIAL_FALSE.hypothesis, TRIVIAL_FALSE.goal)
    assert cm is not None and cm.n == 2 and has_model
    assert is_countermodel(TRIVIAL_FALSE.hypothesis, TRIVIAL_FALSE.goal, cm.n, cm.table)


def test_linear_family_and_affine_form():
    cm = linear_countermodel(COMM_FALSE.hypothesis, COMM_FALSE.goal, time_budget=10)
    assert cm is not None and cm.affine_form() is not None
    assert is_countermodel(COMM_FALSE.hypothesis, COMM_FALSE.goal, cm.n, cm.table)


def test_complete_searches_agree():
    h, g = KNOWN_FALSE.hypothesis, KNOWN_FALSE.goal
    dl = time.monotonic() + 60
    t_cells, ex_cells = find_model_cells(h, g, 3, dl)
    t_sat, ex_sat = find_model_sat(h, g, 3, dl)
    assert (t_cells is None) == (t_sat is None)
    for t in (t_cells, t_sat):
        if t is not None:
            assert is_countermodel(h, g, 3, t)
    if t_cells is None:
        assert ex_cells and ex_sat


def test_exhaustion_verdict_is_a_proof():
    # a True implication has no countermodel at any size
    h, g = ORDER5_A.hypothesis, ORDER5_A.goal
    table, exhausted = decide_size(h, g, 3, time.monotonic() + 60)
    assert table is None and exhausted
    est, real = sat_clause_estimate(h, g, 3), len(sat_encode(h, g, 3)[1])
    assert real / 2 <= est <= real * 2


def test_ladder_reports_facts_and_verifies():
    facts = SearchFacts()
    cm = find_countermodel(KNOWN_FALSE.hypothesis, KNOWN_FALSE.goal, time_budget=60, facts=facts)
    assert cm is not None and is_countermodel(KNOWN_FALSE.hypothesis, KNOWN_FALSE.goal, cm.n, cm.table)
    code = certs.false_code(cm.n, cm.table, KNOWN_FALSE.hypothesis, KNOWN_FALSE.goal)
    assert f"Fin {cm.n}" in code and "decide" in code


def test_austin_pair_has_a_residue_affine_model_but_no_small_finite_one():
    m = residue_affine_countermodel(AUSTIN.hypothesis, AUSTIN.goal, time_budget=30)
    assert m is not None and m.m == 2
    for x in range(40):
        for y in range(40):
            for z in range(12):
                env = {"x": x, "y": y, "z": z}
                assert AUSTIN.hypothesis.evaluate(m.op, env)
    assert not AUSTIN.goal.evaluate(m.op, dict(zip(AUSTIN.goal.variables, m.witness)))
    table, exhausted = decide_size(AUSTIN.hypothesis, AUSTIN.goal, 4, time.monotonic() + 60)
    assert table is None and exhausted
    code = certs.false_nat_residue_code(AUSTIN.hypothesis, m.m, m.A, m.B, m.C, m.witness, AUSTIN.goal)
    assert "grind" in code and "decide" in code
