# Library benchmark — artifacts/bench-stress-2026-09-01-standalone

200 problems, Lean-checked certificates.

| category | n | correct | wrong | no answer | median s | max s |
|---|---|---|---|---|---|---|
| order4_extra_hard | 50 | 50 | 0 | 0 | 383.7 | 400.9 |
| order4_hard | 50 | 50 | 0 | 0 | 0.3 | 403.4 |
| order4_normal | 50 | 50 | 0 | 0 | 0.3 | 35.5 |
| order5_normal | 50 | 50 | 0 | 0 | 0.3 | 469.7 |

**Total: 200/200 correct, 0 wrong, 0 unanswered.**

## Stages

- scan: 71
- eqsat-goal: 40
- finite-model: 29
- eqsat-singleton: 28
- singleton-forcing: 22
- eqsat-goal+lemmas: 6
- superposition: 2
- seeded-grind(wide,4): 1
- eqsat-singleton+lemmas: 1

LLM calls: 0

## Misses / wrong


## Timing and setup

- v0.2.0 **self-contained certificates** (no judge library, no Mathlib):
  every certificate compiled with `lean` (elan, `leanprover/lean4:v4.33.1`)
  through `eqtheory.lean.check`; 4 shards; LLM round armed (never reached).
- Identical verdicts and stage distribution to the judge-library run
  (`../bench-stress-2026-09-01`); per-problem wall median 0.4 s (was 1.4 s —
  a standalone compile loads no library oleans), p90 392 s, max 470 s,
  sum 12 467 s.
- The ~384 s median of `order4_extra_hard` is unchanged: ladder order
  (e-graph queries + superposition before the model finder), not search
  power — see the note in the first report.
