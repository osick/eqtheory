# Lean 4 certificates

The judge compiles a submission against a generated module

```lean
import JudgeMagma.Magma
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x y z : G), <hypothesis>
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x y z : G), <goal>
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G        -- true
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G  -- false
```

and expects `def submission : Goal`. `eqtheory.lean.check.problem_module`
reproduces this module for the optional compile check.

## True

```lean
import JudgeProblem
set_option maxRecDepth 20000

def submission : Goal := by
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
  `grind` as the finisher — used when the explicit chain is not found
  but `grind` closes the goal from the lemmas.
* **singleton forcing**: `have singleton : ∀ (a b : G), a = b := …`.

## False, finite

```lean
import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def submission : Goal := by
  let m : Magma (Fin 4) := {
    op := finOpTable "[[0, 2, 0, 2], [0, 2, 0, 2], [1, 3, 1, 3], [1, 3, 1, 3]]"
  }
  refine ⟨Fin 4, m, ?_⟩
  decideFin!
```

`finOpTable` reads **one digit per entry**, so tables are emitted only for
n ≤ 10. Above that an affine model is spelled in closed form:

```lean
op := fun i j => ⟨Nat.mod (Nat.add (Nat.add (Nat.mul 4 i.val) (Nat.mul 8 j.val)) 0) 11,
                  Nat.mod_lt _ (Nat.succ_pos 10)⟩
```

The named spelling matters: the judge's proof policy is a **declaration
allowlist** (`Nat.*`, `Fin.*`, `List.*`, `Lean.*`, `Mathlib.*`,
`MemoFinOp.*`, `JudgeDecide.*`, `submission.*`, …). The infix operators
`+ * %` elaborate to `HAdd.hAdd` / `HMul.hMul` / `HMod.hMod` and
`by decide` on `0 < n` to `LT.lt` — none allowlisted — so the "obvious"
`(4 * i + 8 * j) % 11` certificate is rejected although it compiles.

## False, infinite (Austin pairs)

```lean
import JudgeProblem
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

def submission : Goal :=
  ⟨Nat, submission.inst, submission.lhs, submission.rhs⟩
```

The law is proved by `grind` after unfolding (case split on the residues,
linear arithmetic), the refutation by a concrete witness and `decide`.
`submission.` is an allowlisted prefix, which is what makes helper
declarations possible. This shape was accepted for the Austin pair
E1167 ⇒ E1763 on the official judge (2026-08-31).

## What the compile check does not do

`eqtheory.lean.check` compiles `JudgeProblem` and the certificate with
`lean -D linter.defProp=false`. It does **not** apply the allowlist, the
banned-token scan (`notation`, `infix`, `run_cmd`, `@[init`, …) or the
nonce-named checked binding of the competition judge. The certificate
generators avoid all of those by construction.
