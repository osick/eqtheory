
from eqtheory import parse_equation, parse_term
from eqtheory.egraph import EGraph, prove_goal, prove_singleton
from eqtheory.proofs import validate
from eqtheory.viz import egraph_to_dot, chain_to_dot, render_egraph


def hyp_tuple(eq):
    return (eq.lhs, eq.rhs, list(eq.variables))


class TestEGraphBasics:
    def test_hash_consing(self):
        g = EGraph()
        a, b = g.add_var("a"), g.add_var("b")
        assert g.add_op(a, b) == g.add_op(a, b)
        assert g.add_var("a") == a

    def test_congruence_closure(self):
        g = EGraph()
        a, b, c = (g.add_var(v) for v in "abc")
        ac, bc = g.add_op(a, c), g.add_op(b, c)
        assert not g.equal(ac, bc)
        g.union(a, b, ("r", "h", (), a)); g.rebuild()
        assert g.equal(ac, bc)

    def test_term_of_round_trip(self):
        g = EGraph()
        t = parse_term("(x ◇ y) ◇ (x ◇ z)")
        assert g.term_of(g.add_term(t)) == t


class TestSaturation:
    # x = x ◇ y   ⟹   x = (x ◇ y) ◇ z   (instantiate twice)
    def test_proves_a_simple_goal_with_a_replayable_chain(self):
        h = parse_equation("x = x ◇ y")
        goal = parse_equation("x = (x ◇ y) ◇ z")
        res = prove_goal(h, goal, time_budget=10)
        assert res is not None
        eg, l, r = res
        lemmas, chain = eg.explain(l, r)
        assert validate(hyp_tuple(h), lemmas, chain, goal.lhs, goal.rhs)

    def test_singleton_forcing(self):
        # x = y forces a singleton
        assert prove_singleton(parse_equation("x = y"), time_budget=5) is not None

    def test_does_not_prove_a_false_goal(self):
        h = parse_equation("x = x ◇ y")
        goal = parse_equation("x = y")
        assert prove_goal(h, goal, time_budget=3, max_rounds=2) is None


class TestViz:
    def test_dot_output(self):
        h = parse_equation("x = x ◇ y")
        eg, l, r = prove_goal(h, parse_equation("x = (x ◇ y) ◇ z"), time_budget=5)
        dot = egraph_to_dot(eg, highlight=[l, r], proof_pairs=[(l, r)])
        assert dot.startswith("digraph egraph") and "cluster_" in dot and "#d62828" in dot

    def test_render_writes_a_file(self, tmp_path):
        h = parse_equation("x = x ◇ y")
        eg, l, r = prove_goal(h, parse_equation("x = (x ◇ y) ◇ z"), time_budget=5)
        out = tmp_path / "egraph.svg"
        used = render_egraph(eg, str(out), highlight=[l, r])
        assert out.exists() and out.stat().st_size > 200
        assert used in ("graphviz", "svg-fallback")
        dot_path = tmp_path / "egraph.dot"
        assert render_egraph(eg, str(dot_path)) == "dot" and dot_path.exists()

    def test_proof_chain_dot(self):
        h = parse_equation("x = x ◇ y")
        eg, l, r = prove_goal(h, parse_equation("x = (x ◇ y) ◇ z"), time_budget=5)
        lemmas, chain = eg.explain(l, r)
        assert chain_to_dot(lemmas, chain).startswith("digraph proof")
