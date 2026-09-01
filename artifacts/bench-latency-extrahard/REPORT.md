# Library benchmark — artifacts/bench-latency-extrahard

50 problems, Lean-checked certificates.

| category | n | correct | wrong | no answer | median s | max s |
|---|---|---|---|---|---|---|
| order4_extra_hard | 50 | 50 | 0 | 0 | 15.4 | 18.2 |

**Total: 50/50 correct, 0 wrong, 0 unanswered.**

## Stages

- finite-model: 25
- eqsat-goal: 25

LLM calls: 0

## Misses / wrong


## Setup and reading

- `Config.latency()` (`--profile latency`): the 15 s countermodel pass
  runs before the proof engines. All 25 False problems are decided by it
  (CDCL at Fin 7–9, 1–14 s incl. the Lean compile); the 25 True problems
  pay the pass in full and then prove via eqsat — hence the ~15.4 s
  median. Default-order comparison: median 383.7 s, max 400.9 s
  (`../bench-stress-2026-09-01-standalone`). Verdicts identical.
