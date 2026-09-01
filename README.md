# eqtheory

A Python library for **equational theories over magmas**: given two
equations in one binary operation `◇`, decide whether the first implies
the second — and hand back a **Lean 4 certificate** either way.

* term rewriting with a ground **Knuth–Bendix order**, one-way matching,
  unification,
* a proof-producing **e-graph** (congruence closure with a proof forest,
  shortest shared explanations) and **equality saturation**,
* **ordered completion** and **goal-directed superposition** with
  replayed proof chains, interreduction and node budgets,
* **finite countermodels**: symbolic linear families, structured tables,
  a complete propagating cell search and a **CDCL** SAT search with
  symmetry breaking (exhaustion verdicts are proofs),
* **infinite countermodels on ℕ** for *Austin pairs* (true in every
  finite magma, false in general),
* **Lean 4 certificates** for every answer, in the shapes accepted by the
  SAIR Stage-2 judge, with an optional compile check,
* an optional, hygienic **LLM stage** with a configurable prompt,
* a **CLI** with e-graph and proof **visualisation** (SVG/PNG/DOT).

The algorithms are those of the SAIR Stage-2 solver (800/800 practice,
see `../docs/paper/`), re-packaged with a clean API. Pure Python 3.11+,
no required dependencies.

```bash
pip install -e .            # from this directory
pip install -e ".[viz,dev]" # graphviz bindings, pytest
```

## Quick start

```python
from eqtheory import Problem, solve

p = Problem.parse("x = y ◇ (x ◇ y)", "x = (x ◇ y) ◇ x")
ans = solve(p)
print(ans.verdict, ans.stage)   # "true" / "false", which engine decided
print(ans.code)                 # the Lean 4 certificate
```

Each engine is a plain function:

```python
from eqtheory import prove_by_superposition, find_countermodel, residue_affine_countermodel, prove_goal
from eqtheory.lean import certs

pr = prove_by_superposition(p.hypothesis, p.goal)       # lemma + instantiation + derived set
cm = find_countermodel(p.hypothesis, p.goal, time_budget=60)   # Countermodel(n, table) or None
nm = residue_affine_countermodel(p.hypothesis, p.goal)  # ℕ model for Austin pairs
eg, l, r = prove_goal(p.hypothesis, p.goal)             # e-graph with the goal sides merged
lemmas, chain = eg.explain(l, r)                        # shared proof, replayable
eg.render("egraph.svg", highlight=(l, r))               # picture
```

## Command line

```bash
eqtheory solve "x = y ◇ (x ◇ y)" "x = (x ◇ y) ◇ x"                # full ladder, prints certificate
eqtheory solve --lean --json ...                                # certificate compiled with Lean
eqtheory prove ...                                              # superposition only
eqtheory model --infinite --cert ...                            # countermodels, finite then ℕ
eqtheory egraph --render egraph.svg --lemmas ...                # saturate and draw the e-graph
eqtheory viz-proof --out proof.dot ...                          # the extracted proof as a graph
eqtheory cert --table "[[0,1],[1,0]]" ...                       # wrap a table as a certificate
```

`--lean` needs `EQTHEORY_LEAN_BIN` (a Lean 4.33 binary) and
`EQTHEORY_JUDGE_ROOT` (a built checkout of the Stage-2 judge library) or
`EQTHEORY_LEAN_PATH`. `--llm` needs `OPENROUTER_API_KEY`.

## Documentation

* [User guide](docs/guide.md) — the pipeline, budgets, composing your own ladder
* [Mathematical background](docs/background.md) — the theory behind each engine, with references
* [Certificates](docs/certificates.md) — the Lean shapes and the proof-policy lessons
* [API overview](docs/api.md)
* `examples/single_file_solver.py` — a complete solver in 60 lines
* `artifacts/` — sample renderings and benchmark reports

## Status

Version 0.1.0 (2026-09-01). Tests: `python -m pytest` (70 tests; the Lean
end-to-end test is skipped unless Lean is configured). Benchmarks with
Lean-checked certificates are in `artifacts/bench-*/REPORT.md`.

License: MIT.
