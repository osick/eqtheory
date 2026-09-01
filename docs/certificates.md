# Lean 4 certificates

Every answer comes with a Lean 4 file that is **self-contained**: it
declares the magma class, the two laws and the goal, and then proves the
goal. Nothing but a Lean 4 toolchain is needed — no Mathlib, no library
of the former competition. The toolchain a certificate is generated for
is a *setting* (`lean_toolchain`, default `leanprover/lean4:v4.33.1`, the
version the shapes were validated with): it is recorded in the file's
first line and, when a certificate is checked with `eqtheory.lean.check`,
written to a `lean-toolchain` file so an elan proxy selects that version.
Set it to `none` to check with whatever `lean` is on the path.

## The header (`certs.prelude`)

```lean
class Magma (α : Type u) where
  op : α → α → α
infixl:65 " ◇ " => Magma.op

@[reducible] def EquationLHS (G : Type) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ y)
@[reducible] def EquationRHS (G : Type) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G          -- true
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G    -- false
```

## True: explicit proof terms

```lean
set_option maxRecDepth 20000
theorem submission : Goal := by
  intro G _ h
  intro x y z
  have lem3 : ∀ (a b : G), … = … := fun a b => (h a b b).trans (congrArg (fun t => t ◇ b) (h …)).symm
  exact (lem3 x y).symm
```

* **e-graph proofs** (`egraph_proof_code`): shared sub-proofs become
  `have eK : s = t := …` lines; the top chain is an `exact` of `.trans`,
  `.symm` and `congrArg (fun t => t ◇ r)` / `congrArg (fun t => l ◇ t)`.
* **superposition proofs** (`superposition_code`): every derived lemma the
  goal lemma depends on is emitted first, in dependency order, as a
  universally quantified `have`; the goal is an instance of the last.
* **seeded grind** (`seeded_grind_bodies`): the same `have` lines with
  `grind` as the finisher.
* **singleton forcing**: `have singleton : ∀ (a b : G), a = b := …`.

## False, finite: a table or a closed form, decided by `decide`

```lean
-- model: table n=4
def submission.table : Array (Array Nat) := #[#[0, 2, 0, 2], #[0, 2, 0, 2], #[1, 3, 1, 3], #[1, 3, 1, 3]]
def submission.op (i j : Fin 4) : Fin 4 :=
  ⟨(submission.table.getD i.val #[]).getD j.val 0 % 4, Nat.mod_lt _ (by decide)⟩
instance submission.inst : Magma (Fin 4) := ⟨submission.op⟩

set_option maxRecDepth 20000
theorem submission : Goal := ⟨Fin 4, submission.inst, by decide, by decide⟩
```

Any size works (`false_table_code`); when the table is affine the closed
form is emitted instead (`false_affine_code`):

```lean
def submission.op (i j : Fin 11) : Fin 11 := ⟨(1 * i.val + 1 * j.val + 1) % 11, Nat.mod_lt _ (by decide)⟩
```

`decide` evaluates every instance in the kernel — n^(variables) cases per
law, seconds up to Fin 12 with three variables.

## False, infinite: an operation on ℕ (Austin pairs)

```lean
-- model: porc m=2 A=[[0, 0], [0, 0]] B=[[1, 1], [1, 1]] C=[[1, -1], [-1, 1]] witness=[0, 1, 0]
def submission.op (a b : Nat) : Nat :=
  if a % 2 = 0 then (if b % 2 = 0 then b + 1 else (b - 1)) else (if b % 2 = 0 then b - 1 else (b + 1))
def submission.inst : Magma Nat := { op := submission.op }

theorem submission.lhs : @EquationLHS Nat submission.inst := by
  intro x y z
  show x = submission.op y (submission.op (submission.op z (submission.op y y)) x)
  simp only [submission.op]
  grind

theorem submission.rhs : ¬ @EquationRHS Nat submission.inst := by
  intro h
  have := h 0 1 0
  revert this; decide

theorem submission : Goal :=
  ⟨Nat, submission.inst, submission.lhs, submission.rhs⟩
```

The law is proved by `grind` after unfolding (case split on the residues,
linear arithmetic), the refutation by a concrete witness and `decide`.

## Checking

```bash
eqtheory solve --lean "x = x ◇ y" "x = (x ◇ y) ◇ z"     # every certificate compiled before it is returned
lean Certificate.lean                                   # or by hand, with any Lean 4 ≥ 4.33
```

`eqtheory.lean.check.compile_certificate(code, cfg)` writes the file and
the `lean-toolchain` pin into a temporary directory and runs `lean`; a
result is accepted only with exit code 0 and no `error`/`sorry` in the
output.

## Historical: the SAIR Stage-2 judge shapes (`style="judge"`)

The competition judge compiled submissions against its own library
(`import JudgeProblem`, `finOpTable` with one digit per entry — hence a
Fin-10 ceiling — `decideFin!`, and a declaration allowlist under which
`(a*i+b*j+c) % n` was rejected while `Nat.mod (Nat.add …)` passed).
`certs.*(…, style="judge")` reproduces those files exactly; checking them
needs that library on `EQTHEORY_LEAN_PATH` or a built checkout under
`EQTHEORY_JUDGE_ROOT`. Nothing else in the library depends on it.
