# User guide

## Problems and terms

A *magma* is a set with one binary operation `◇`; no law holds unless the
hypothesis states it. An *equation* is `s = t` over variables `a–z`,
implicitly universally quantified. A *problem* is an implication
"hypothesis ⇒ goal": does every magma satisfying the hypothesis satisfy
the goal?

```python
from eqtheory import Problem, parse_term, render_term
p = Problem.parse("x = (y ◇ (z ◇ (z ◇ (x ◇ z)))) ◇ z", "x = (x ◇ y) ◇ (((z ◇ z) ◇ z) ◇ z)")
p.hypothesis.variables      # ('x', 'y', 'z') — first-appearance order = Lean binder order
t = parse_term("(x ◇ y) ◇ x")   # nested tuples: (('x','y'),'x'); variables are strings
```

Terms are plain tuples; `match`, `unify`, `substitute`, `positions`,
`replace_at`, `kbo_greater` operate on them.

## The default ladder

`solve(problem, Config(), judge=None, complete=None, trace=None)` runs:

| stage | engine | answers |
|---|---|---|
| singleton-forcing | syntactic: `x = t` with `x ∉ t` | true |
| scan | all tables on Fin 2–3 | false |
| eqsat-singleton / eqsat-goal (± lemmas) | equality saturation, staged instantiation caps | true |
| superposition | ordered completion ladder, goal-directed | true |
| finite-models | linear families → structured → complete search ≤ Fin 12 (`max_model_n`) | false |
| infinite-models | residue-class affine models on ℕ | false |
| seeded-grind *(judge)* | derived lemmas as `have`s + `grind` | true |
| llm *(complete)* | one LLM round, verified | either |

Every stage is a function `stage_*` in `eqtheory.solve` that returns an
`Answer(verdict, code, stage, verified, model)` or `None`. Compose your
own order by calling them directly.

A `judge(verdict, code) -> bool` callback (`eqtheory.lean.check.make_judge(cfg)`)
enables the Lean-dependent stages and re-checks every certificate before
it is returned. A `Completer` (`prompt -> str`, e.g.
`eqtheory.llm.OpenRouterClient()`) adds the LLM round.

`Trace` collects per-stage timings, the search facts (sizes *proven* free
of countermodels) and the list of stages that failed — the negative
knowledge the LLM prompt is built from.

## Configuration

Every default that is a choice rather than a theorem lives in
`eqtheory.config.Settings`: the Lean toolchain the certificates are
pinned to (`lean_toolchain`, `None` = no pin), the Lean binary and
timeout, `maxRecDepth`, the finite-search reach (`model_max_n`), the SAT
memory budget, and the LLM defaults (model, endpoint, key variable, seed,
effort, rounds). Resolution order, later wins:

1. the shipped defaults,
2. a TOML file: `EQTHEORY_CONFIG`, else `./eqtheory.toml`, else
   `~/.config/eqtheory/config.toml` (see `eqtheory.toml.example`),
3. environment variables `EQTHEORY_<FIELD>` (e.g. `EQTHEORY_LEAN_TOOLCHAIN`,
   `EQTHEORY_MODEL_MAX_N`; `none`/empty clears an optional field),
4. `eqtheory.configure(lean_toolchain="leanprover/lean4:v4.34.0", model_max_n=14)`.

`eqtheory config` prints the effective values and where each comes from.
Settings are read at call time, so a `configure(...)` applies to the
next certificate immediately.

## Budgets

`Config.latency()` is the low-latency profile: a short countermodel pass
(default 15 s: linear families plus the complete Fin 4–5 rungs) runs
right after the scan, so False problems with small models are answered in
seconds instead of waiting behind the proof engines. The default order
keeps the proof engines first (the competition tuning). CLI:
`eqtheory solve --profile latency …`.

`Config` fields: `eqsat_budget` (s, per query), `superposition_ladder`
(tuples `(size_cap, rounds, node_budget, max_lemmas, interreduce)`),
`superposition_budget`, `model_budget`, `max_model_n`, `infinite_budget`,
`grind_seed_budget`, `llm_rounds`, `inst_caps`.

The completion engine is budgeted in *candidate equations*, not seconds,
so a run is reproducible on any machine; deadlines are only backstops.

## Using the engines directly

```python
from eqtheory import derive_lemmas, Budget, prove_by_superposition
lemmas = derive_lemmas(p.hypothesis, Budget(max_lemmas=60, size_cap=13, rounds=6, nodes=4000, interreduce=True))
pr = prove_by_superposition(p.hypothesis, p.goal)      # SuperpositionProof or None
```

```python
from eqtheory.models import find_countermodel, SearchFacts, decide_size
facts = SearchFacts()
cm = find_countermodel(p.hypothesis, p.goal, time_budget=60, facts=facts)
facts.exhausted            # sizes with provably no countermodel
table, done = decide_size(p.hypothesis, p.goal, 6, deadline)   # one size, complete
```

```python
from eqtheory import prove_goal
eg, l, r = prove_goal(p.hypothesis, p.goal, time_budget=10, inst_cap=20_000)
lemmas, chain = eg.explain(l, r)          # ('e1', s, t, sub-chain) lemmas + top chain
eg.render("egraph.png", highlight=(l, r), proof_pairs=((l, r),))
```

## Certificates

`eqtheory.lean.certs` renders proofs and models as self-contained Lean 4
files (see [certificates.md](certificates.md)); each declares the
`Magma` class and the two laws, so a plain toolchain checks it:

```python
from eqtheory.lean import check as lean_check
cfg = lean_check.configure()                 # finds lean on PATH / elan / EQTHEORY_LEAN_BIN
res = lean_check.compile_certificate(ans.code, cfg)   # CheckResult(ok, verdict, seconds, output)
judge = lean_check.make_judge(cfg)           # judge(verdict, code) -> bool for solve(...)
```

The historical SAIR judge shapes are available with `style="judge"`.

## LLM stage

```python
from eqtheory.llm import llm_stage, OpenRouterClient, DEFAULT_PROMPT, load_prompt
out = llm_stage(p, OpenRouterClient(model="openai/gpt-oss-120b", seed=0, reasoning_effort="low"),
                judge=judge, max_rounds=4, prompt=load_prompt("my_prompt.txt"))
```

The template uses the placeholders `{hypothesis} {goal} {search_facts}
{tried} {round} {previous_attempts}` (braces in Lean/JSON examples are
doubled). False proposals are verified numerically inside the library;
True proposals need the judge, otherwise they come back `verified=False`.

## Visualisation

`eqtheory egraph --render out.svg` draws every e-class as a cluster (goal
classes highlighted, the found equality in red). With the `graphviz`
Python package and a `dot` binary you get SVG/PNG/PDF; without them an
SVG fallback is produced and `--dot` writes the graph for later
rendering. `eqtheory viz-proof --out proof.dot` draws the extracted
proof's shared-lemma DAG.
