# Changelog

## 0.3.1 (2026-09-01)
- Housekeeping: removed leftover references to the solver's private
  development repository and its paper from README and docs; dropped the
  one-time repository-export script; `docs/releasing.md` is now just
  "CI and releases". No code changes.

## 0.3.0 (2026-09-01)
- `Config.latency()` / `eqtheory solve --profile latency`: a short
  countermodel pass before the proof engines. Measured on the stress
  set's extra_hard family (Lean-checked): median 383.7 s → 15.4 s, max
  400.9 s → 18.2 s, verdicts identical
  (`artifacts/bench-latency-extrahard/REPORT.md`).

## 0.2.0 (2026-09-01)
- **Self-contained certificates.** Every Lean certificate now declares the
  `Magma` class, the two laws and the goal itself and checks with a plain
  Lean 4 toolchain (core only, no Mathlib, no competition library). The
  Stage-2 judge shapes remain available as `style="judge"`.
- Finite countermodels of **any size** are certifiable (table as
  `Array (Array Nat)` + `decide`); the Fin-10 ceiling was a judge artefact.
  Default search reach `DEFAULT_MAX_N = 12`.
- `eqtheory.lean.check`: needs only a `lean` binary (PATH, elan, or
  `EQTHEORY_LEAN_BIN`); pins the validated toolchain with a
  `lean-toolchain` file; `make_judge(cfg)` no longer needs the problem.
- New `tests/test_lean.py`: every certificate shape compiled with a real
  toolchain; CI installs Lean via elan and runs them. Stress set re-run
  with the new certificates: 200/200, identical stage distribution
  (`artifacts/bench-stress-2026-09-01-standalone/REPORT.md`).
- README logo generated from a real solve (`scripts/make_logo.py`), PyPI
  badges and install instructions.
- `eqtheory.config`: no fixed versions or defaults in code — toolchain,
  Lean binary/timeout/recursion depth, search reach, SAT memory and LLM
  defaults resolve defaults → TOML → `EQTHEORY_*` env → `configure()`;
  `eqtheory config` shows the effective values.

## 0.1.0 (2026-09-01)
First release — the Stage-2 solver's algorithms as a library. Validated
200/200 on the Stage-2 stress set with Lean-checked certificates
(`artifacts/bench-stress-2026-09-01/REPORT.md`).
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
- CI (pyflakes, pytest+coverage, build) and tag-driven release workflow
  (GitHub Release + PyPI trusted publishing); `docs/limitations.md`.
