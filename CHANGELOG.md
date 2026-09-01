# Changelog

## 0.1.0 (2026-09-01)
First release — the Stage-2 solver's algorithms as a library.
- `terms`: parser/renderer, matching, unification, ground KBO.
- `egraph` + `proofs`: proof-producing e-graph, equality saturation with
  instantiation/collapse passes, shortest shared explanations, chain replay.
- `completion`: ordered completion with critical pairs, interreduction,
  node budgets, goal-directed superposition ladder, grind seeds.
- `models.finite`: exhaustive scan, symbolic linear families, structured
  tables, complete propagating cell search, CDCL with symmetry breaking.
- `models.infinite`: residue-class affine models on ℕ (Austin pairs).
- `lean.certs`: all judge-accepted certificate shapes; `lean.check`:
  optional compile check against the judge library.
- `llm`: configurable prompt, preflight, dedupe, numeric verification of
  countermodels, OpenRouter client.
- `solve`: the default ladder; `cli`: solve/prove/model/egraph/viz-proof/cert.
- `viz`: e-graph and proof-graph rendering (graphviz, SVG fallback).
