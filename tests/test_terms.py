import itertools

import pytest

from eqtheory import (Equation, Problem, parse_term, render_term, parse_equation,
                      term_vars, term_leaves, positions, replace_at, match, unify,
                      substitute, kbo_greater, holds)
from eqtheory.terms import resolve


def T(s):
    return parse_term(s)


class TestParsing:
    def test_round_trip(self):
        for s in ("x", "x ◇ y", "(x ◇ y) ◇ z", "x ◇ (y ◇ (z ◇ x))"):
            assert render_term(T(s)) == render_term(T(render_term(T(s))))

    def test_star_is_accepted(self):
        assert T("x * (y * z)") == T("x ◇ (y ◇ z)")

    def test_left_associative(self):
        assert T("x ◇ y ◇ z") == (("x", "y"), "z")

    def test_bad_term(self):
        with pytest.raises(ValueError):
            T("x ◇")

    def test_equation_binder_order(self):
        e = parse_equation("x = (y ◇ (z ◇ x)) ◇ w")
        assert e.variables == ("x", "y", "z", "w")

    def test_problem_parse(self):
        p = Problem.parse("x = x ◇ y", "x = y")
        assert isinstance(p.hypothesis, Equation) and p.goal.text == "x = y"


class TestStructure:
    def test_vars_and_leaves(self):
        t = T("(x ◇ y) ◇ (x ◇ z)")
        assert term_vars(t) == ["x", "y", "z"] and term_leaves(t) == 4

    def test_positions_pre_order(self):
        t = T("(x ◇ y) ◇ z")
        paths = [p for p, _ in positions(t)]
        assert paths == [(), (0,), (0, 0), (0, 1), (1,)]

    def test_replace_at(self):
        assert replace_at(T("(x ◇ y) ◇ z"), (0, 1), "w") == (("x", "w"), "z")

    def test_holds_on_a_finite_magma(self):
        op = lambda a, b: (a + b) % 2
        assert holds(parse_equation("x ◇ y = y ◇ x"), op, 2)
        assert not holds(parse_equation("x = x ◇ y"), op, 2)


class TestMatchAndUnify:
    def test_match_is_one_way(self):
        pat, term = T("a ◇ b"), T("(x ◇ y) ◇ z")
        assert match(pat, term) is not None
        assert match(term, pat) is None

    def test_repeated_variable_must_agree(self):
        assert match(T("a ◇ a"), T("x ◇ x")) is not None
        assert match(T("a ◇ a"), T("x ◇ y")) is None

    def test_goal_variable_never_binds(self):
        assert match(T("a ◇ b"), "x") is None

    def test_unify_binds_both_sides(self):
        s = unify(T("a ◇ b"), T("x ◇ (y ◇ z)"))
        assert resolve(T("a ◇ b"), s) == T("x ◇ (y ◇ z)")

    def test_unify_occurs_check(self):
        assert unify("a", T("a ◇ b")) is None

    def test_substitute_leaves_free_vars(self):
        assert substitute(T("a ◇ b"), {"a": "x"}) == ("x", "b")


class TestKBO:
    TERMS = [T(s) for s in ("x", "x ◇ x", "x ◇ y", "(x ◇ x) ◇ x", "x ◇ (x ◇ x)",
                            "((x ◇ y) ◇ z) ◇ w", "(x ◇ y) ◇ (z ◇ w)")]

    def test_fewer_leaves_wins(self):
        assert kbo_greater(T("(x ◇ y) ◇ z"), T("x ◇ y"))
        assert not kbo_greater(T("x ◇ y"), T("(x ◇ y) ◇ z"))

    def test_irreflexive_and_asymmetric(self):
        for a in self.TERMS:
            assert not kbo_greater(a, a)
            for b in self.TERMS:
                if kbo_greater(a, b):
                    assert not kbo_greater(b, a)

    def test_transitive_on_sample(self):
        for a, b, c in itertools.product(self.TERMS, repeat=3):
            if kbo_greater(a, b) and kbo_greater(b, c):
                assert kbo_greater(a, c)

    def test_distinct_variables_incomparable(self):
        assert not kbo_greater("x", "y") and not kbo_greater("y", "x")

    def test_stable_under_context(self):
        s, t = T("(x ◇ x) ◇ x"), T("x ◇ (x ◇ x)")
        big, small = (s, t) if kbo_greater(s, t) else (t, s)
        assert kbo_greater(("y", (big, "z")), ("y", (small, "z")))
