"""``solve(problem)``: the algorithms composed in the order that worked.

Every stage is also a public function returning ``None`` or a
:class:`Answer`; compose your own ladder if the default does not fit.
The default order (cheapest and most decisive first):

1. singleton forcing (``x = t`` with ``x ∉ t`` collapses the magma),
2. exhaustive scan of Fin 2–3 for a countermodel,
3. equality saturation: singleton query, then the goal query, plain
   and with derived lemmas (staged instantiation caps),
4. goal-directed superposition over the completion ladder,
5. finite countermodels (linear families, structured tables, complete
   cell/CDCL search up to Fin 10),
6. infinite countermodels on ℕ (Austin pairs),
7. seeded ``grind`` (needs a Lean ``judge``),
8. an LLM round (needs a ``Completer``; True answers need the judge).

Nothing here consults a stored table of results; every answer is derived
from the two equations at hand and comes with a Lean certificate.
"""
from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Callable

from . import completion, egraph, llm as llm_mod
from .config import settings
from .lean import certs
from .models import finite, infinite
from .terms import Problem, render_term, term_vars

Judge = Callable[[str, str], bool]


@dataclass
class Answer:
    verdict: str                 # "true" | "false"
    code: str                    # Lean certificate
    stage: str
    verified: bool = True        # False only for an LLM proof no judge checked
    model: object = None         # Countermodel / NatResidueModel for "false"


@dataclass
class Config:
    eqsat_budget: float = 25.0
    superposition_ladder: tuple = completion.DEFAULT_LADDER
    superposition_budget: float = 300.0
    model_budget: float = 60.0
    max_model_n: int = field(default_factory=lambda: settings.model_max_n)
    infinite_budget: float = 20.0
    grind_seed_budget: float = 60.0
    llm_rounds: int = field(default_factory=lambda: settings.llm_rounds)
    inst_caps: tuple = (20_000, 75_000, 300_000)


@dataclass
class Trace:
    steps: list = field(default_factory=list)
    facts: finite.SearchFacts = field(default_factory=finite.SearchFacts)
    tried: list = field(default_factory=list)

    def log(self, stage: str, seconds: float, note: str = ""):
        self.steps.append((stage, round(seconds, 3), note))


# ── stages ───────────────────────────────────────────────────────────────

def stage_singleton_forcing(problem: Problem) -> Answer | None:
    hyp, goal = problem.hypothesis, problem.goal
    if not isinstance(hyp.lhs, str) or hyp.lhs in term_vars(hyp.rhs):
        return None
    v = hyp.lhs
    args = lambda w: " ".join(w if u == v else "a" for u in hyp.variables)
    proof = (f"intro {' '.join(goal.variables)}\n" if goal.variables else "") + \
        f"have singleton : ∀ (a b : G), a = b := fun a b => (h {args('a')}).trans (h {args('b')}).symm\n" \
        f"exact singleton ({render_term(goal.lhs)}) ({render_term(goal.rhs)})"
    return Answer("true", certs.true_code(proof, hyp, goal), "singleton-forcing")


def stage_scan(problem: Problem, max_n: int = 3) -> Answer | None:
    cm, _ = finite.scan(problem.hypothesis, problem.goal, max_n)
    return Answer("false", certs.false_code(cm.n, cm.table, problem.hypothesis, problem.goal), "scan", model=cm) if cm else None


def _staged(query, hyp, budget, caps, *args, lemmas=()):
    deadline = time.monotonic() + budget
    for cap in caps:
        left = deadline - time.monotonic()
        if left <= 1.0:
            return None
        res = query(hyp, *args, lemmas=lemmas, time_budget=left, inst_cap=cap)
        if res is not None:
            return res
    return None


def stage_eqsat_singleton(problem: Problem, cfg: Config = Config(), with_lemmas: bool = False) -> Answer | None:
    hyp, goal = problem.hypothesis, problem.goal
    derived = completion.derive_lemmas(hyp) if with_lemmas else []
    res = _staged(egraph.prove_singleton, hyp, cfg.eqsat_budget, cfg.inst_caps, lemmas=derived)
    if res is None:
        return None
    eg, a, b = res
    ex = eg.explain(a, b)
    if ex is None:
        return None
    lemmas, chain = ex
    rules = {l["name"]: (l["lhs"], l["rhs"], tuple(l["vars"])) for l in derived}
    used = certs._used_names(lemmas, chain)
    lem_lines = certs.lemma_haves(hyp, derived, used) if used else []
    lines, expr, end = certs.shared_proof_lines(hyp, lemmas, chain, "a", rules)
    if lem_lines is None or expr is None or end != "b":
        return None
    block = "".join(f"  {ln}\n" for ln in lem_lines + lines)
    proof = (f"intro {' '.join(goal.variables)}\n" if goal.variables else "") + \
        f"have singleton : ∀ (a b : G), a = b := by\n  intro a b\n{block}  exact {expr}\n" \
        f"exact singleton {render_term(goal.lhs)} {render_term(goal.rhs)}"
    return Answer("true", certs.true_code(proof, hyp, goal), "eqsat-singleton" + ("+lemmas" if with_lemmas else ""))


def stage_eqsat_goal(problem: Problem, cfg: Config = Config(), with_lemmas: bool = False) -> Answer | None:
    hyp, goal = problem.hypothesis, problem.goal
    derived = completion.derive_lemmas(hyp) if with_lemmas else []
    res = _staged(egraph.prove_goal, hyp, cfg.eqsat_budget, cfg.inst_caps, goal, lemmas=derived)
    if res is None:
        return None
    eg, l, r = res
    ex = eg.explain(l, r)
    if ex is None:
        return None
    lemmas, chain = ex
    code = certs.egraph_proof_code(hyp, goal, lemmas, chain, derived)
    return Answer("true", code, "eqsat-goal" + ("+lemmas" if with_lemmas else "")) if code else None


def stage_superposition(problem: Problem, cfg: Config = Config()) -> Answer | None:
    pr = completion.prove_by_superposition(problem.hypothesis, problem.goal, cfg.superposition_ladder,
                                           deadline=time.monotonic() + cfg.superposition_budget)
    if pr is None:
        return None
    code = certs.superposition_code(problem.hypothesis, problem.goal, pr)
    return Answer("true", code, "superposition") if code else None


def stage_finite_models(problem: Problem, cfg: Config = Config(), facts: finite.SearchFacts | None = None) -> Answer | None:
    cm = finite.find_countermodel(problem.hypothesis, problem.goal, time_budget=cfg.model_budget,
                                  max_n=cfg.max_model_n, facts=facts)
    return Answer("false", certs.false_code(cm.n, cm.table, problem.hypothesis, problem.goal), "finite-model", model=cm) if cm else None


def stage_infinite_models(problem: Problem, cfg: Config = Config()) -> Answer | None:
    m = infinite.residue_affine_countermodel(problem.hypothesis, problem.goal, time_budget=cfg.infinite_budget)
    if m is None:
        return None
    code = certs.false_nat_residue_code(problem.hypothesis, m.m, m.A, m.B, m.C, m.witness, problem.goal)
    return Answer("false", code, "nat-residue-model", model=m)


def stage_seeded_grind(problem: Problem, judge: Judge, cfg: Config = Config(), tried: list | None = None) -> Answer | None:
    seeds = completion.seed_lemmas(problem.hypothesis, deadline=time.monotonic() + cfg.grind_seed_budget)
    for label, body in certs.seeded_grind_bodies(problem.hypothesis, problem.goal, list(seeds)):
        code = certs.true_code(body, problem.hypothesis, problem.goal)
        if judge("true", code):
            return Answer("true", code, label)
        if tried is not None:
            tried.append(label)
    return None


def stage_llm(problem: Problem, complete: llm_mod.Completer, judge: Judge | None = None, cfg: Config = Config(),
              facts: finite.SearchFacts | None = None, tried=(), prompt: str = llm_mod.DEFAULT_PROMPT) -> Answer | None:
    facts = facts or finite.SearchFacts()
    out = llm_mod.llm_stage(problem, complete, judge=judge, max_rounds=cfg.llm_rounds, prompt=prompt,
                            search_facts=llm_mod.format_search_facts(facts.exhausted, facts.searched),
                            tried="\n".join(f"- {t}" for t in tried))
    return Answer(out.verdict, out.code, "llm", verified=out.verified) if out.verdict else None


# ── the pipeline ─────────────────────────────────────────────────────────

def solve(problem: Problem | tuple[str, str], cfg: Config = Config(), *, judge: Judge | None = None,
          complete: llm_mod.Completer | None = None, trace: Trace | None = None) -> Answer | None:
    """Run the default ladder. ``judge(verdict, code) -> bool`` (see
    :func:`eqtheory.lean.check.make_judge`) enables the Lean-dependent
    stages (seeded grind, verified LLM proofs) and re-checks every
    certificate before it is returned. Certificates are self-contained
    Lean 4 files (:mod:`eqtheory.lean.certs`)."""
    if not isinstance(problem, Problem):
        problem = Problem.parse(*problem)
    tr = trace if trace is not None else Trace()

    def run(name, fn):
        t0 = time.monotonic()
        try:
            ans = fn()
        except (ValueError, RecursionError, MemoryError) as err:
            tr.log(name, time.monotonic() - t0, f"error: {err}")
            return None
        tr.log(name, time.monotonic() - t0, ans.stage if ans else "no answer")
        if ans is None:
            tr.tried.append(name)
            return None
        if judge is not None and ans.verified and not judge(ans.verdict, ans.code):
            tr.log(name, time.monotonic() - t0, "certificate rejected by Lean")
            return None
        return ans

    ladder = [
        ("singleton-forcing", lambda: stage_singleton_forcing(problem)),
        ("scan", lambda: stage_scan(problem)),
        ("eqsat-singleton", lambda: stage_eqsat_singleton(problem, cfg)),
        ("eqsat-goal", lambda: stage_eqsat_goal(problem, cfg)),
        ("eqsat-goal+lemmas", lambda: stage_eqsat_goal(problem, cfg, with_lemmas=True)),
        ("eqsat-singleton+lemmas", lambda: stage_eqsat_singleton(problem, cfg, with_lemmas=True)),
        ("superposition", lambda: stage_superposition(problem, cfg)),
        ("finite-models", lambda: stage_finite_models(problem, cfg, tr.facts)),
        ("infinite-models", lambda: stage_infinite_models(problem, cfg)),
    ]
    if judge is not None:
        ladder.append(("seeded-grind", lambda: stage_seeded_grind(problem, judge, cfg, tr.tried)))
    if complete is not None:
        ladder.append(("llm", lambda: stage_llm(problem, complete, judge, cfg, tr.facts, tr.tried)))
    for name, fn in ladder:
        ans = run(name, fn)
        if ans is not None:
            return ans
    return None
