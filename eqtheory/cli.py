"""Command line: ``eqtheory solve|egraph|model|cert|prove|viz-proof``."""
from __future__ import annotations

import argparse
import json
import sys
import time

from . import __version__, completion, egraph, llm as llm_mod, viz
from .solve import solve as run_solve, Config, Trace
from .lean import certs, check as lean_check
from .models import finite, infinite
from .terms import Problem


def _problem(a) -> Problem:
    return Problem.parse(a.hypothesis, a.goal)


def _judge(a):
    if not getattr(a, "lean", False):
        return None
    cfg = lean_check.configure(timeout=a.lean_timeout)
    if cfg is None:
        sys.exit("Lean not configured: set EQTHEORY_LEAN_BIN and EQTHEORY_JUDGE_ROOT (or EQTHEORY_LEAN_PATH)")
    pr = _problem(a)
    return lean_check.make_judge(pr.hypothesis, pr.goal, cfg)


def cmd_solve(a):
    pr = _problem(a)
    cfg = Config(model_budget=a.model_budget, superposition_budget=a.superposition_budget,
                           eqsat_budget=a.eqsat_budget, infinite_budget=a.infinite_budget, llm_rounds=a.llm_rounds)
    complete = None
    if a.llm:
        complete = llm_mod.OpenRouterClient(model=a.llm_model, seed=a.llm_seed, reasoning_effort=a.llm_effort)
    tr = Trace()
    t0 = time.monotonic()
    ans = run_solve(pr, cfg, judge=_judge(a), complete=complete, trace=tr)
    out = {"hypothesis": pr.hypothesis.text, "goal": pr.goal.text, "seconds": round(time.monotonic() - t0, 2),
           "verdict": ans.verdict if ans else None, "stage": ans.stage if ans else None,
           "verified": ans.verified if ans else None,
           "facts": {"exhausted": tr.facts.exhausted, "searched": tr.facts.searched},
           "trace": tr.steps}
    if a.json:
        out["code"] = ans.code if ans else None
        print(json.dumps(out, ensure_ascii=False, indent=2))
        return
    print(f"{pr.hypothesis.text}  ⇒  {pr.goal.text}")
    for stage, sec, note in tr.steps:
        print(f"  {stage:24s} {sec:8.2f}s  {note}")
    if ans is None:
        print("no answer")
        return
    print(f"verdict: {ans.verdict}  (stage {ans.stage}{'' if ans.verified else ', UNVERIFIED'})")
    if a.out:
        open(a.out, "w", encoding="utf-8").write(ans.code)
        print(f"certificate written to {a.out}")
    else:
        print(ans.code)


def cmd_egraph(a):
    pr = _problem(a)
    lemmas = completion.derive_lemmas(pr.hypothesis) if a.lemmas else []
    eg, l, r, ok = egraph.saturate(pr.hypothesis, pr.goal.variables, (pr.goal.lhs, pr.goal.rhs), lemmas=lemmas,
                                   time_budget=a.budget, inst_cap=a.inst_cap, max_rounds=a.rounds)
    n_classes = len(eg.classes())
    print(f"e-graph: {len(eg.nodes)} nodes, {n_classes} classes, goal sides {'merged' if ok else 'NOT merged'}")
    if a.render:
        kind = viz.render_egraph(eg, a.render, highlight=(l, r), proof_pairs=((l, r),) if ok else (),
                                 max_classes=a.max_classes)
        print(f"rendered ({kind}) → {a.render}")
    if a.dot:
        open(a.dot, "w", encoding="utf-8").write(viz.egraph_to_dot(eg, highlight=(l, r), max_classes=a.max_classes))
        print(f"dot → {a.dot}")


def cmd_model(a):
    pr = _problem(a)
    facts = finite.SearchFacts()
    cm = finite.find_countermodel(pr.hypothesis, pr.goal, time_budget=a.budget, max_n=a.max_n, facts=facts)
    if cm is not None:
        print(f"countermodel on Fin {cm.n}:")
        for row in cm.table:
            print("  " + " ".join(str(v) for v in row))
        aff = cm.affine_form()
        if aff:
            print(f"  affine: (a·i + b·j + c) mod n with (a, b, c) = {aff}")
        if a.cert:
            print(certs.false_code(cm.n, cm.table))
        return
    print(f"no finite countermodel found; sizes proven empty: {facts.exhausted}, swept: {facts.searched}")
    if a.infinite:
        m = infinite.residue_affine_countermodel(pr.hypothesis, pr.goal, time_budget=a.budget)
        if m is None:
            print("no residue-class affine model on ℕ")
            return
        print(f"ℕ model: m={m.m} A={m.A} B={m.B} C={m.C} witness={m.witness}")
        if a.cert:
            print(certs.false_nat_residue_code(pr.hypothesis, m.m, m.A, m.B, m.C, m.witness))


def cmd_prove(a):
    pr = _problem(a)
    t0 = time.monotonic()
    proof = completion.prove_by_superposition(pr.hypothesis, pr.goal, deadline=time.monotonic() + a.budget)
    if proof is None:
        print(f"no superposition proof within {a.budget}s")
        return
    print(f"proved by {proof.lemma['name']} in {time.monotonic() - t0:.1f}s "
          f"({len(proof.derived)} lemmas derived)")
    code = certs.superposition_code(pr.hypothesis, pr.goal, proof)
    print(code)


def cmd_cert(a):
    pr = _problem(a)
    if a.table:
        table = json.loads(a.table)
        if not finite.is_countermodel(pr.hypothesis, pr.goal, len(table), table):
            sys.exit("the table is not a countermodel of this problem")
        print(certs.false_code(len(table), table))
    elif a.proof:
        print(certs.true_code(open(a.proof, encoding="utf-8").read()))
    else:
        sys.exit("give --table or --proof")


def cmd_viz_proof(a):
    pr = _problem(a)
    res = egraph.prove_goal(pr.hypothesis, pr.goal, time_budget=a.budget)
    if res is None:
        sys.exit("saturation did not connect the goal sides")
    eg, l, r = res
    lemmas, chain = eg.explain(l, r)
    dot = viz.chain_to_dot(lemmas, chain, title=f"{pr.hypothesis.text} ⇒ {pr.goal.text}")
    open(a.out, "w", encoding="utf-8").write(dot)
    print(f"proof graph (dot) → {a.out}; {len(lemmas)} shared lemmas, chain length {len(chain)}")


def main(argv=None):
    p = argparse.ArgumentParser(prog="eqtheory", description="equational theories over magmas")
    p.add_argument("--version", action="version", version=f"eqtheory {__version__}")
    sub = p.add_subparsers(dest="cmd", required=True)

    def common(sp, lean=False):
        sp.add_argument("hypothesis", help='e.g. "x = y ◇ (x ◇ y)"')
        sp.add_argument("goal")
        if lean:
            sp.add_argument("--lean", action="store_true", help="check certificates with Lean (EQTHEORY_* env)")
            sp.add_argument("--lean-timeout", type=float, default=300.0)

    s = sub.add_parser("solve", help="run the full ladder"); common(s, lean=True)
    s.add_argument("--json", action="store_true"); s.add_argument("--out", help="write the certificate here")
    s.add_argument("--model-budget", type=float, default=60.0); s.add_argument("--superposition-budget", type=float, default=300.0)
    s.add_argument("--eqsat-budget", type=float, default=25.0); s.add_argument("--infinite-budget", type=float, default=20.0)
    s.add_argument("--llm", action="store_true", help="add an LLM round (OPENROUTER_API_KEY)")
    s.add_argument("--llm-model", default="openai/gpt-oss-120b"); s.add_argument("--llm-seed", type=int, default=0)
    s.add_argument("--llm-effort", default="low"); s.add_argument("--llm-rounds", type=int, default=4)
    s.set_defaults(fn=cmd_solve)

    s = sub.add_parser("egraph", help="saturate and render the e-graph"); common(s)
    s.add_argument("--render", metavar="FILE", help="image output (.svg/.png/.pdf; graphviz optional)")
    s.add_argument("--dot", metavar="FILE"); s.add_argument("--lemmas", action="store_true")
    s.add_argument("--budget", type=float, default=10.0); s.add_argument("--inst-cap", type=int, default=20_000)
    s.add_argument("--rounds", type=int, default=8); s.add_argument("--max-classes", type=int, default=200)
    s.set_defaults(fn=cmd_egraph)

    s = sub.add_parser("model", help="search countermodels"); common(s)
    s.add_argument("--budget", type=float, default=60.0); s.add_argument("--max-n", type=int, default=finite.MAX_TABLE_N)
    s.add_argument("--infinite", action="store_true", help="also try the ℕ residue-class family")
    s.add_argument("--cert", action="store_true", help="print the Lean certificate")
    s.set_defaults(fn=cmd_model)

    s = sub.add_parser("prove", help="goal-directed superposition"); common(s)
    s.add_argument("--budget", type=float, default=300.0); s.set_defaults(fn=cmd_prove)

    s = sub.add_parser("cert", help="wrap a table or a tactic body as a certificate"); common(s)
    s.add_argument("--table", help="JSON table"); s.add_argument("--proof", help="file with a tactic body")
    s.set_defaults(fn=cmd_cert)

    s = sub.add_parser("viz-proof", help="render an e-graph proof as a dot graph"); common(s)
    s.add_argument("--out", required=True); s.add_argument("--budget", type=float, default=10.0)
    s.set_defaults(fn=cmd_viz_proof)

    a = p.parse_args(argv)
    a.fn(a)


if __name__ == "__main__":
    main()
