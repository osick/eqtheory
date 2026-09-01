# Limitations

## Theoretical

- **Undecidability.** Whether one magma law implies another is
  undecidable in general (the word problem for one-equation theories can
  encode arbitrary computation). Every engine here is a semi-decision
  procedure with a budget: a "no answer" is exactly that, never a verdict.
- **Finite search is incomplete for False.** The finite model finders
  are complete *per size* (an exhausted size is a proof that no
  countermodel of that size exists), but an implication can be false only
  in infinite magmas (Austin pairs). The ℕ engine covers one family of
  such models — residue-class affine operations with small coefficients —
  not all of them.
- **Proof search is incomplete for True.** Equality saturation is
  bounded by the instantiation pool and the node caps; ordered
  completion is bounded by lemma size and candidate count. Unfair
  completion (budgets in candidate equations, goal-directed stop) trades
  refutational completeness for predictability.
- **One binary operation.** Terms have one symbol `◇` and variables
  `a–z`; no constants, no second operation, no built-in laws. The KBO is
  the ground order for that signature; the e-matching, the SAT encoding
  and the certificate shapes all assume it.
- **Certificates fix the logic.** A True answer is a Lean term built
  from `h`, `.trans`, `.symm`, `congrArg` (and `grind` on lemma seeds);
  a False answer is an explicit finite table, an affine closed form or
  the ℕ construction. There
  is no other kind of proof object, so the library cannot express, for
  example, a countermodel that is only known to exist non-constructively.

## Pragmatic

- **`decide` cost grows with the model.** A table certificate is checked
  by Lean's kernel evaluating every instance: n^(variables) cases per law.
  Fin 12 with three variables is ~1 700 cases (seconds); Fin 20 with four
  variables is 160 000 and needs `decide +kernel` or a smarter proof.
  (The old Fin-10 ceiling was a judge artefact and is gone.)
- **Fin 9–10 complete search is expensive.** The CDCL encoding grows as
  n^(variables) × n³; four-variable laws at Fin 9 need hundreds of
  megabytes. The memory estimate switches to the cell search, which can
  then run out of time rather than memory.
- **Budgets are wall-clock for the model finders**, so the exhaustion
  verdicts (`SearchFacts.exhausted`) depend on the machine; the
  completion engine's node budgets do not.
- **`grind`-based certificates depend on the Lean version.** The
  explicit-chain certificates are stable; `grind` (seeded grind, the ℕ
  law) behaves differently across Lean releases. The default
  `lean_toolchain` setting is the validated version; change it when you
  validate another.
- **The compile check trusts Lean, nothing else.** A certificate that
  compiles without `sorry` is a proof; the check does not sandbox the
  file, so only compile certificates you generated or read.
- **The LLM stage is a last resort, measured near zero.** On the
  Stage-2 residue the model solved 0 of 18 open problems in 144 calls;
  its value is hygiene (verified countermodels, no repeats), not reach.
  True proposals are only trusted with a Lean judge; without one they
  are returned `verified=False`.
- **Pure Python.** Everything is single-threaded CPython; the slowest
  stress-set problem takes ~7 minutes in the default ladder. The ladder
  order is tuned for the Stage-2 distribution (many small countermodels,
  many short proofs); a different distribution may want a different order
  — every stage is a public function for that reason.
- **Parsing is strict.** Equations use `◇` (or `*`, normalised),
  single-letter variables and parentheses; no implicit associativity.
