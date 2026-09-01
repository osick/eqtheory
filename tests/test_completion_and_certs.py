import time

from eqtheory import Problem, parse_equation, parse_term
from eqtheory.completion import (Budget, derive_lemmas, goal_instance, prove_by_superposition,
                                 rewrite_step, seed_lemmas)
from eqtheory.egraph import prove_goal
from eqtheory.lean import certs
from eqtheory.proofs import validate

ORDER5_A = Problem.parse("x = (y ◇ (z ◇ (z ◇ (x ◇ z)))) ◇ z", "x = (x ◇ y) ◇ (((z ◇ z) ◇ z) ◇ z)")
LIVE_0152 = Problem.parse("x = ((y ◇ z) ◇ ((y ◇ y) ◇ z)) ◇ x", "x = y ◇ (x ◇ ((z ◇ (x ◇ y)) ◇ x))")
AUSTIN = Problem.parse("x = y ◇ ((z ◇ (y ◇ y)) ◇ x)", "x = (y ◇ z) ◇ ((x ◇ z) ◇ x)")
KNOWN_FALSE = Problem.parse("x = (y ◇ x) ◇ (x ◇ z)", "x = y ◇ (x ◇ (y ◇ z))")


def T(s):
    return parse_term(s)


def rules_from(eqs):
    out = []
    for i, (src, dst) in enumerate(eqs):
        vs = list(dict.fromkeys(c for t in (src, dst) for c in str(t) if c.isalpha()))
        out.append((f"r{i}", None, src, dst, tuple(vs), True))
    return out


class TestRewriting:
    def test_weight_preserving_step_fires_in_kbo_direction_only(self):
        rules = rules_from([(T("(a ◇ a) ◇ a"), T("a ◇ (a ◇ a)"))])
        assert rewrite_step(T("(x ◇ x) ◇ x"), rules)[0] == T("x ◇ (x ◇ x)")
        assert rewrite_step(T("x ◇ (x ◇ x)"), rules_from([(T("a ◇ (a ◇ a)"), T("(a ◇ a) ◇ a"))])) is None

    def test_commutativity_on_distinct_variables_never_fires(self):
        assert rewrite_step(T("x ◇ y"), rules_from([(T("a ◇ b"), T("b ◇ a"))])) is None


class TestDerivation:
    def test_every_lemma_replays(self):
        hyp = ORDER5_A.hypothesis
        lemmas = derive_lemmas(hyp, Budget(60, 13, 6, 4000, None, True))
        assert lemmas
        rules = {l["name"]: (l["lhs"], l["rhs"], tuple(l["vars"])) for l in lemmas}
        for lem in lemmas:
            assert validate((hyp.lhs, hyp.rhs, list(hyp.variables)), [], lem["chain"], lem["lhs"], lem["rhs"], rules)

    def test_node_budget_is_deterministic(self):
        seen = [[], []]
        for k in range(2):
            derive_lemmas(ORDER5_A.hypothesis, Budget(10_000, 13, 3, 500), on_candidate=seen[k].append)
        assert len(seen[0]) == len(seen[1]) <= 500


class TestSuperposition:
    def test_proves_a_real_order5_problem(self):
        pr = prove_by_superposition(ORDER5_A.hypothesis, ORDER5_A.goal)
        assert pr is not None
        code = certs.superposition_code(ORDER5_A.hypothesis, ORDER5_A.goal, pr)
        assert code and "exact" in code and code.startswith("import JudgeProblem")

    def test_never_proves_a_known_false_implication(self):
        assert prove_by_superposition(KNOWN_FALSE.hypothesis, KNOWN_FALSE.goal,
                                      deadline=time.monotonic() + 15) is None

    def test_goal_instance_flipped(self):
        lem = {"name": "l", "vars": ("a",), "lhs": T("a ◇ a"), "rhs": "a", "chain": []}
        args, flipped = goal_instance(lem, "p", T("p ◇ p"))
        assert flipped and args == ("p",)


class TestCertificates:
    def test_seeded_grind_bodies_have_universal_lemmas(self):
        seeds = list(seed_lemmas(LIVE_0152.hypothesis, deadline=time.monotonic() + 20))
        bodies = certs.seeded_grind_bodies(LIVE_0152.hypothesis, LIVE_0152.goal, seeds)
        assert bodies and all(b.endswith("grind") and "∀" in b for _, b in bodies)

    def test_false_code_forms(self):
        assert "finOpTable" in certs.false_code(2, [[0, 0], [0, 0]])
        n = 11
        code = certs.false_code(n, [[(4 * i + 8 * j) % n for j in range(n)] for i in range(n)])
        assert "Nat.mod (Nat.add" in code and " % " not in code and "by decide" not in code

    def test_nat_residue_certificate_matches_the_verified_shape(self):
        code = certs.false_nat_residue_code(AUSTIN.hypothesis, 2, [[0, 0], [0, 0]], [[1, 1], [1, 1]],
                                            [[1, -1], [-1, 1]], (0, 1, 0))
        assert "def submission.op (a b : Nat) : Nat :=" in code
        assert "if a % 2 = 0 then (if b % 2 = 0 then b + 1 else (b - 1)) else (if b % 2 = 0 then b - 1 else (b + 1))" in code
        assert "show x = submission.op y (submission.op (submission.op z (submission.op y y)) x)" in code
        assert "⟨Nat, submission.inst, submission.lhs, submission.rhs⟩" in code

    def test_egraph_proof_certificate(self):
        h, g = parse_equation("x = x ◇ y"), parse_equation("x = (x ◇ y) ◇ z")
        eg, l, r = prove_goal(h, g, time_budget=5)
        lemmas, chain = eg.explain(l, r)
        code = certs.egraph_proof_code(h, g, lemmas, chain)
        assert code and "intro x y z" in code and "exact" in code
