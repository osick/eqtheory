# Mathematical background

This chapter states the theory each engine rests on and where it comes
from. Every reference below is a published paper or book, or an arXiv
preprint with its identifier; the ones marked *(validated 2026-08)* were
checked against the source when the accompanying paper was written.

## 1. Equational logic and magmas

A magma is a set with one binary operation. Equational implications
between magma laws are the subject of the **Equational Theories Project**
[ETP25](#ETP25), which classified all 22 028 942 implications among the 4 694
laws with at most four operations, and of Tao's 2026 distillation
challenge [Tao26](#Tao26) that asks for *explainable* solvers. The completeness
theorem of equational logic [Birkhoff35](#Birkhoff35) is what makes both sides of an
answer certifiable: an implication holds iff the goal is derivable by
substitution, congruence and transitivity from the hypothesis — a finite
proof object — and fails iff some model of the hypothesis violates the goal.

An implication that holds in every *finite* magma but fails in some
infinite one is an **Austin pair** [Austin66](#Austin66); the ETP lists them
explicitly. No table search of any size can refute one; §5 is for them.

## 2. Term rewriting and the Knuth–Bendix order

Orienting equations into rewrite rules and completing the set with
critical pairs is the Knuth–Bendix procedure [KnuthBendix70](#KnuthBendix70); the
textbook treatment (termination orders, critical pairs, confluence) is
Baader–Nipkow [BaaderNipkow98](#BaaderNipkow98). The library uses a *ground* KBO on the
one-symbol signature: weight = leaf count, ties broken by variable
multiset comparison and a lexicographic path fallback — a strict,
well-founded, monotone order. It gates `rewrite_step` so interreduction
always terminates, and it orients weight-preserving equations in one
consistent direction.

*Ordered completion / superposition* — completion that never fails to
orient because inferences are restricted by the order — is due to
Bachmair and Ganzinger [BachmairGanzinger94](#BachmairGanzinger94). `derive_lemmas` is a
proof-producing instance: each critical pair carries the chain "undo rule
A, apply rule B under the overlap position", replayed before acceptance.
Mature provers built on the same calculus, which set the reference for
what the residue looks like, are Vampire [KovacsVoronkov13](#KovacsVoronkov13),
E [Schulz19](#Schulz19) and Twee [Smallbone21](#Smallbone21); their behaviour on the ETP is
reported in [Janota25](#Janota25) and [Janota26](#Janota26).

## 3. Congruence closure, e-graphs, equality saturation

Congruence closure decides ground equalities [NelsonOppen80](#NelsonOppen80); storing
the reason for every union in a *proof forest* makes it proof-producing
[NieuwenhuisOliveras05](#NieuwenhuisOliveras05) — that is exactly the `union(u, v, reason)` /
`explain(u, v)` pair in `EGraph`. Equality saturation — repeatedly
e-matching rewrite rules against the whole e-graph and merging, with
rebuilding deferred to a batch — is the egg design [Willsey21](#Willsey21). The
library's saturation adds two things specific to magma laws: an
*instantiation pass* that grounds the hypothesis over a bounded pool of
terms, and a *collapse pass* that merges instances whose difference is a
variable free on one side of the hypothesis. Explanations are shortest
paths in the proof forest (Dijkstra, congruence steps weighted), with
shared sub-explanations named once and referenced (`ref` links).

## 4. Finite model finding

Finite model search by cell assignment with propagation and the *Least
Number Heuristic* (a new cell may introduce at most one new element) is
the SEM/Mace design [ZhangZhang95](#ZhangZhang95), [McCune03](#McCune03). `find_model_cells`
implements it with *watched instances* (a ground instance is re-checked
only when a cell it is blocked on is assigned) and unit propagation.

The SAT route encodes "some n-element magma satisfies the hypothesis and
refutes the goal" with one-hot cell variables and a per-instance
selector, and adds a *value-symmetry ladder* ("value v may appear only
after v−1 has") that removes the n! renamings of every model; complete
symmetry breaking for finite models is studied in [Danco25](#Danco25). The solver
is a compact CDCL: two watched literals, first-UIP conflict analysis and
clause learning [MarquesSilva99](#MarquesSilva99), [Moskewicz01](#Moskewicz01), [Zhang01](#Zhang01), activity
branching with phase saving, geometric restarts. SAT attacks on
equational problems of this kind are the subject of [Subercaseaux26](#Subercaseaux26)
and [Kondylidou26](#Kondylidou26).

Both searches are *complete*: an empty result within the budget is a
proof that no countermodel of that size exists (`SearchFacts.exhausted`).

## 5. Infinite countermodels

For an Austin pair the library searches residue-class affine operations
on ℕ, `op(x, y) = A[r][s]·x + B[r][s]·y + C[r][s]` with `r = x mod m`,
`s = y mod m` — the shape of the ETP's hand-built infinite models
(translation-like operations on parity classes). The candidate is
checked numerically on small ranges (necessary evidence only) and then
*proved* in Lean: after unfolding, `grind` performs the residue case
split and linear arithmetic, and a concrete witness with `decide`
refutes the goal.

## 6. Certificates in Lean 4

Lean 4 [deMouraUllrich21](#deMouraUllrich21) with Mathlib [mathlib20](#mathlib20) is the checker.
Proofs are explicit terms (`.trans`, `.symm`, `congrArg`) with `have`s
for shared lemmas, so they are independent of tactic heuristics; `grind`
is used only as a finisher on lemma seeds and in the ℕ-model law. The
judge shapes are documented in [certificates.md](certificates.md).

## 7. LLM stage

The measured lesson (Stage-2 residue, 2026-08: 0 of 18 open problems
solved by the model in 144 calls) is that the LLM is a last resort whose
value lies in the hygiene around it: exact negative knowledge, verified
countermodels, no repeated proposals. Cazares [Cazares26](#Cazares26) documents the
single-prompt ceiling of LLM mathematical reasoning; Berlioz–Melliès
[Berlioz26](#Berlioz26) study the latent structure of equational theories.

## References

- <a id="Austin66"></a>[Austin66] A. K. Austin. *Finite Models for Laws in Two Variables.* Proc. AMS 17 (1966), 1410–1412.
- <a id="BaaderNipkow98"></a>[BaaderNipkow98] F. Baader, T. Nipkow. *Term Rewriting and All That.* Cambridge University Press, 1998.
- <a id="BachmairGanzinger94"></a>[BachmairGanzinger94] L. Bachmair, H. Ganzinger. *Rewrite-Based Equational Theorem Proving with Selection and Simplification.* J. Logic and Computation 4(3) (1994), 217–247.
- <a id="Berlioz26"></a>[Berlioz26] L. Berlioz, P.-A. Melliès. *The Latent Space of Equational Theories.* arXiv:2601.20759 (2026).
- <a id="Birkhoff35"></a>[Birkhoff35] G. Birkhoff. *On the Structure of Abstract Algebras.* Proc. Cambridge Phil. Soc. 31 (1935), 433–454.
- <a id="Cazares26"></a>[Cazares26] M. I. Cazares. *Less Is More: Cognitive Load and the Single-Prompt Ceiling in LLM Mathematical Reasoning.* arXiv:2604.18897 (2026).
- <a id="Danco25"></a>[Danco25] M. Dančo, M. Janota, M. Codish, J. J. Araújo. *Complete Symmetry Breaking for Finite Models.* AAAI 39 (2025), 11194–11202.
- <a id="deMouraUllrich21"></a>[deMouraUllrich21] L. de Moura, S. Ullrich. *The Lean 4 Theorem Prover and Programming Language.* CADE 28, LNCS 12699 (2021), 625–635. doi:10.1007/978-3-030-79876-5_37
- <a id="ETP25"></a>[ETP25] M. Bolan, J. Breitner, …, T. Tao, … *The Equational Theories Project: Advancing Collaborative Mathematical Research at Scale.* arXiv:2512.07087 (2025).
- <a id="Janota25"></a>[Janota25] M. Janota. *Experimental Results for Vampire on the Equational Theories Project.* arXiv:2508.15856 (2025).
- <a id="Janota26"></a>[Janota26] M. Janota, M. Rawson, S. Schulz. *Case Study: Saturations as Explicit Models in Equational Theories.* arXiv:2602.16324 (2026).
- <a id="KnuthBendix70"></a>[KnuthBendix70] D. E. Knuth, P. B. Bendix. *Simple Word Problems in Universal Algebras.* In: Computational Problems in Abstract Algebra, Pergamon (1970), 263–297.
- <a id="Kondylidou26"></a>[Kondylidou26] L. Kondylidou, J. Blanchette, M. J. H. Heule. *Tao's Equational Proof Challenge Accepted.* arXiv:2605.21200 (2026).
- <a id="KovacsVoronkov13"></a>[KovacsVoronkov13] L. Kovács, A. Voronkov. *First-Order Theorem Proving and Vampire.* CAV 2013, LNCS 8044, 1–35.
- <a id="MarquesSilva99"></a>[MarquesSilva99] J. P. Marques-Silva, K. A. Sakallah. *GRASP: A Search Algorithm for Propositional Satisfiability.* IEEE Trans. Computers 48(5) (1999), 506–521.
- <a id="mathlib20"></a>[mathlib20] The mathlib Community. *The Lean Mathematical Library.* CPP 2020. doi:10.1145/3372885.3373824
- <a id="McCune03"></a>[McCune03] W. McCune. *Mace4 Reference Manual and Guide.* ANL/MCS-TM-264 (2003), arXiv:cs/0310055.
- <a id="Moskewicz01"></a>[Moskewicz01] M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang, S. Malik. *Chaff: Engineering an Efficient SAT Solver.* DAC 2001, 530–535.
- <a id="NelsonOppen80"></a>[NelsonOppen80] G. Nelson, D. C. Oppen. *Fast Decision Procedures Based on Congruence Closure.* J. ACM 27(2) (1980), 356–364.
- <a id="NieuwenhuisOliveras05"></a>[NieuwenhuisOliveras05] R. Nieuwenhuis, A. Oliveras. *Proof-Producing Congruence Closure.* RTA 2005, LNCS 3467, 453–468.
- <a id="Schulz19"></a>[Schulz19] S. Schulz, S. Cruanes, P. Vukmirović. *Faster, Higher, Stronger: E 2.3.* CADE 27, LNCS 11716 (2019), 495–507.
- <a id="Smallbone21"></a>[Smallbone21] N. Smallbone. *Twee: An Equational Theorem Prover.* CADE 28, LNCS 12699 (2021), 602–613.
- <a id="Subercaseaux26"></a>[Subercaseaux26] B. Subercaseaux, B. Przybocki. *A SAT Attack on Tarski's High School Algebra Problem.* arXiv:2608.08421 (2026).
- <a id="Tao26"></a>[Tao26] T. Tao. *Mathematics Distillation Challenge — Equational Theories.* Blog post, 13 March 2026.
- <a id="Willsey21"></a>[Willsey21] M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock, P. Panchekha. *egg: Fast and Extensible Equality Saturation.* PACMPL 5 (POPL) (2021). doi:10.1145/3434304
- <a id="Zhang01"></a>[Zhang01] L. Zhang, C. F. Madigan, M. H. Moskewicz, S. Malik. *Efficient Conflict Driven Learning in a Boolean Satisfiability Solver.* ICCAD 2001, 279–285. doi:10.1109/ICCAD.2001.968634
- <a id="ZhangZhang95"></a>[ZhangZhang95] J. Zhang, H. Zhang. *SEM: A System for Enumerating Models.* IJCAI 95.
