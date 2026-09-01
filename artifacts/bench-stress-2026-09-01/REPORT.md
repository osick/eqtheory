# Library benchmark — artifacts/bench-stress-2026-09-01

200 problems, Lean-checked certificates.

| category | n | correct | wrong | no answer | median s | max s |
|---|---|---|---|---|---|---|
| order4_extra_hard | 50 | 50 | 0 | 0 | 385.4 | 401.4 |
| order4_hard | 50 | 50 | 0 | 0 | 1.5 | 404.9 |
| order4_normal | 50 | 50 | 0 | 0 | 1.4 | 35.6 |
| order5_normal | 50 | 50 | 0 | 0 | 1.3 | 493.4 |

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

- Setup: 4 shards in parallel (`run.sh`), default `Config()`, every
  certificate compiled with Lean 4.33.1 against the Stage-2 judge library
  (upstream 817a465) via `eqtheory.lean.check`; LLM round armed
  (OpenRouter `openai/gpt-oss-120b`, effort low) — never reached.
- Per-problem wall: median 1.4 s, p90 394 s, max 493 s
  (`order5_normal_0036`, seeded grind); sum 12 643 s, ≈ 53 min wall on 4 shards.
- The ~385 s median of `order4_extra_hard` is the ladder order, not the
  model finder: those are False problems whose Fin-7–9 countermodels are
  found by CDCL in seconds, but the default ladder spends the e-graph
  queries (4 × 25 s) and the superposition ladder (300 s) first. A short
  finite-model pass before superposition would cut this family to well
  under a minute; left as a follow-up tuning of `Config` (the solver's
  original order was validated for the competition clock, not for latency).
