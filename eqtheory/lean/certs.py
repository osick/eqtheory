"""Lean 4 certificate generation.

Default style ``"standalone"``: every certificate is a **self-contained
Lean 4 file** — it declares the ``Magma`` class, the two laws and the
goal itself and needs nothing but a Lean 4 toolchain (no Mathlib, no
external library). True answers are explicit proof terms; finite
countermodels are tables (any size) or affine closed forms checked by
``decide``; infinite countermodels are ℕ operations whose law is proved
by ``grind`` and refuted by a witness.

Style ``"judge"`` reproduces the shapes accepted by the SAIR Stage-2
judge (2026-08), which compiled against its own library
(``import JudgeProblem``, ``finOpTable`` with one digit per entry — hence
:data:`MAX_FINOPTABLE_N` —, ``decideFin!``, and a declaration allowlist
that forced ``Nat.mod (Nat.add …)`` spellings). Kept for reproducing the
competition results; not needed otherwise.
"""
from __future__ import annotations

import json
from typing import Mapping, Sequence

from ..config import settings
from ..proofs import Chain
from ..terms import Equation, Term, render_term, substitute

MAX_FINOPTABLE_N = 10      # a property of the historical judge's finOpTable


def _rec_depth() -> str:
    return f"set_option maxRecDepth {settings.lean_max_rec_depth}\n"


# ── proof chains → Lean terms ────────────────────────────────────────────

def render_chain(chain: Chain, cur: Term, hyp: tuple, env: Mapping[str, tuple], rules=None):
    """Render a chain to one Lean proof term; returns (expr, end_term).
    Empty chains (refl) return (None, cur)."""
    exprs = []
    for link in chain:
        expr, cur = _render_link(link, cur, hyp, env, rules)
        if expr is not None:
            exprs.append(expr)
    if not exprs:
        return None, cur
    out = exprs[0]
    for nxt in exprs[1:]:
        out = f"({out}).trans ({nxt})"
    return out, cur


def _render_link(link, cur, hyp, env, rules=None):
    if link[0] == "h":
        _, sigma, forward = link
        args = " ".join(render_term(t) for t in sigma)
        expr = f"h {args}" if forward else f"(h {args}).symm"
        HL, HR, hvars = hyp
        sub = dict(zip(hvars, sigma))
        return expr, substitute(HR if forward else HL, sub)
    if link[0] == "lem":
        _, name, sigma, forward = link
        LL, RR, rvars = rules[name]
        args = " ".join(render_term(t) for t in sigma)
        expr = f"{name} {args}" if forward else f"({name} {args}).symm"
        sub = dict(zip(rvars, sigma))
        return expr, substitute(RR if forward else LL, sub)
    if link[0] == "ref":
        _, name, flipped = link
        s, e = env[name]
        return (f"{name}.symm", s) if flipped else (name, e)
    l, r = cur
    el, l2 = render_chain(link[1], l, hyp, env, rules)
    er, r2 = render_chain(link[2], r, hyp, env, rules)
    if el is None and er is None:
        return None, cur
    if el is not None and er is None:
        return f"congrArg (fun t => t ◇ {render_term(r)}) ({el})", (l2, r)
    if el is None:
        return f"congrArg (fun t => {render_term(l)} ◇ t) ({er})", (l, r2)
    return (f"(congrArg (fun t => t ◇ {render_term(r)}) ({el}))"
            f".trans (congrArg (fun t => {render_term(l2)} ◇ t) ({er}))"), (l2, r2)


def _used_names(lemmas: list, chain: Chain) -> set:
    """Derived-lemma names referenced by an e-graph proof."""
    used: set = set()

    def scan(links):
        for link in links:
            if link[0] == "lem":
                used.add(link[1])
            elif link[0] == "cong":
                scan(link[1]); scan(link[2])
    for _, _, _, sub in lemmas:
        scan(sub)
    scan(chain)
    return used


def _hyp_tuple(hyp: Equation):
    return (hyp.lhs, hyp.rhs, list(hyp.variables))


def _deps(lem) -> set:
    out: set = set()

    def scan(links):
        for link in links:
            if link[0] == "lem":
                out.add(link[1])
            elif link[0] == "cong":
                scan(link[1]); scan(link[2])
    scan(lem["chain"])
    return out


def emission_order(derived: Sequence[dict], used: set):
    """Lemmas to emit, dependencies first; None on a cycle or a dangling
    reference (Lean has no forward references)."""
    by_name = {lem["name"]: lem for lem in derived}
    order, state = [], {}

    def visit(name):
        if state.get(name) == 1:
            return True
        if state.get(name) == 0:
            return False
        lem = by_name.get(name)
        if lem is None:
            return False
        state[name] = 0
        for dep in sorted(_deps(lem)):
            if not visit(dep):
                return False
        state[name] = 1
        order.append(lem)
        return True
    for name in sorted(used):
        if not visit(name):
            return None
    return order


def lemma_haves(hyp: Equation, derived: Sequence[dict], used: set) -> list[str] | None:
    """``have lemK : ∀ (…: G), lhs = rhs := fun … => proof`` lines,
    dependencies first."""
    rules = {lem["name"]: (lem["lhs"], lem["rhs"], tuple(lem["vars"])) for lem in derived}
    ordered = emission_order(derived, used)
    if ordered is None:
        return None
    lines = []
    for lem in ordered:
        expr, endt = render_chain(lem["chain"], lem["lhs"], _hyp_tuple(hyp), {}, rules)
        if expr is None or endt != lem["rhs"]:
            return None
        binders = " ".join(lem["vars"])
        lines.append(f"have {lem['name']} : ∀ ({binders} : G), "
                     f"{render_term(lem['lhs'])} = {render_term(lem['rhs'])} := fun {binders} => {expr}")
    return lines


def shared_proof_lines(hyp: Equation, lemmas: list, chain: Chain, start: Term, rules=None):
    """Render an e-graph proof: (have_lines, top_expr, end_term)."""
    env: dict = {}
    lines = []
    for name, s, e, sub in lemmas:
        expr, endt = render_chain(sub, s, _hyp_tuple(hyp), env, rules)
        if endt != e or expr is None:
            return None, None, None
        lines.append(f"have {name} : {render_term(s)} = {render_term(e)} := {expr}")
        env[name] = (s, e)
    top, end = render_chain(chain, start, _hyp_tuple(hyp), env, rules)
    return lines, top, end


# ── certificate bodies ───────────────────────────────────────────────────

STANDALONE, JUDGE = "standalone", "judge"
DEFAULT_STYLE = STANDALONE


def _binders(eq: Equation) -> str:
    return " ".join(f"({v} : G)" for v in eq.variables)


def prelude(hyp: Equation, goal: Equation, verdict: str) -> str:
    """The self-contained header: ``Magma``, the two laws, the ``Goal``."""
    target = ("∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G" if verdict == "true"
              else "∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G")
    pin = f" (generated for {settings.lean_toolchain})" if settings.lean_toolchain else ""
    return (f"-- eqtheory certificate: self-contained, checks with a plain Lean 4 toolchain{pin}\n"
            "class Magma (α : Type u) where\n  op : α → α → α\n"
            'infixl:65 " ◇ " => Magma.op\n\n'
            f"@[reducible] def EquationLHS (G : Type) [Magma G] : Prop := ∀ {_binders(hyp)}, {hyp.text}\n"
            f"@[reducible] def EquationRHS (G : Type) [Magma G] : Prop := ∀ {_binders(goal)}, {goal.text}\n"
            f"abbrev Goal : Prop := {target}\n\n")


def _style(style, hyp, goal):
    style = style or DEFAULT_STYLE
    if style == STANDALONE and (hyp is None or goal is None):
        raise ValueError("standalone certificates need the hypothesis and the goal")
    if style not in (STANDALONE, JUDGE):
        raise ValueError(f"unknown certificate style {style!r}")
    return style


def is_standalone(code: str) -> bool:
    return not code.startswith("import JudgeProblem")


def true_code(proof_body: str, hyp: Equation | None = None, goal: Equation | None = None, *,
              style: str | None = None, max_heartbeats: int | None = None) -> str:
    """Wrap a tactic body (after ``intro G _ h``) into a certificate."""
    style = _style(style, hyp, goal)
    lines = proof_body.strip().split("\n")
    indented = "\n".join("  " + ln if ln.strip() else "" for ln in lines)
    opts = _rec_depth()
    if max_heartbeats is not None:
        opts += f"set_option maxHeartbeats {int(max_heartbeats)}\n"
    if style == JUDGE:
        return f"import JudgeProblem\n{opts}\ndef submission : Goal := by\n  intro G _ h\n{indented}\n"
    return f"{prelude(hyp, goal, 'true')}{opts}\ntheorem submission : Goal := by\n  intro G _ h\n{indented}\n"


def _affine_form(n: int, table):
    c = table[0][0] % n
    a = (table[1][0] - c) % n if n > 1 else 0
    b = (table[0][1] - c) % n if n > 1 else 0
    for i in range(n):
        for j in range(n):
            if table[i][j] % n != (a * i + b * j + c) % n:
                return None
    return a, b, c


def false_table_code(n: int, table, hyp: Equation | None = None, goal: Equation | None = None, *,
                     style: str | None = None) -> str:
    """Finite countermodel as an explicit table. Standalone: any size, the
    table is an ``Array (Array Nat)`` and both facts are decided by
    ``decide``. Judge: ``finOpTable`` (n ≤ MAX_FINOPTABLE_N) + ``decideFin!``."""
    style = _style(style, hyp, goal)
    if style == JUDGE:
        return ("import JudgeProblem\nimport JudgeDecide.DecideBang\nimport JudgeFinOp.MemoFinOp\nopen MemoFinOp\n"
                f"{_rec_depth()}set_option maxHeartbeats 0\n\n"
                "def submission : Goal := by\n"
                f"  let m : Magma (Fin {n}) := {{\n    op := finOpTable \"{json.dumps(table)}\"\n  }}\n"
                f"  refine ⟨Fin {n}, m, ?_⟩\n  decideFin!\n")
    rows = ", ".join("#[" + ", ".join(str(v) for v in row) + "]" for row in table)
    return (f"{prelude(hyp, goal, 'false')}"
            f"-- model: table n={n}\n"
            f"def submission.table : Array (Array Nat) := #[{rows}]\n"
            f"def submission.op (i j : Fin {n}) : Fin {n} :=\n"
            f"  ⟨(submission.table.getD i.val #[]).getD j.val 0 % {n}, Nat.mod_lt _ (by decide)⟩\n"
            f"instance submission.inst : Magma (Fin {n}) := ⟨submission.op⟩\n\n"
            f"{_rec_depth()}"
            f"theorem submission : Goal := ⟨Fin {n}, submission.inst, by decide, by decide⟩\n")


def false_affine_code(n: int, a: int, b: int, c: int, hyp: Equation | None = None, goal: Equation | None = None, *,
                      style: str | None = None) -> str:
    """Affine countermodel (a·i + b·j + c) mod n in closed form."""
    style = _style(style, hyp, goal)
    if style == JUDGE:
        return ("import JudgeProblem\nimport JudgeDecide.DecideBang\n"
                f"{_rec_depth()}set_option maxHeartbeats 0\n\n"
                "def submission : Goal := by\n"
                f"  let m : Magma (Fin {n}) := {{\n"
                f"    op := fun i j => ⟨Nat.mod (Nat.add (Nat.add (Nat.mul {a} i.val) (Nat.mul {b} j.val)) {c}) {n}, "
                f"Nat.mod_lt _ (Nat.succ_pos {n - 1})⟩\n  }}\n"
                f"  refine ⟨Fin {n}, m, ?_⟩\n  decideFin!\n")
    return (f"{prelude(hyp, goal, 'false')}"
            f"-- model: affine n={n} a={a} b={b} c={c}\n"
            f"def submission.op (i j : Fin {n}) : Fin {n} := ⟨({a} * i.val + {b} * j.val + {c}) % {n}, Nat.mod_lt _ (by decide)⟩\n"
            f"instance submission.inst : Magma (Fin {n}) := ⟨submission.op⟩\n\n"
            f"{_rec_depth()}"
            f"theorem submission : Goal := ⟨Fin {n}, submission.inst, by decide, by decide⟩\n")


def false_code(n: int, table, hyp: Equation | None = None, goal: Equation | None = None, *,
               style: str | None = None) -> str:
    """Closed affine form when the table has one, the table otherwise
    (judge style: table only up to MAX_FINOPTABLE_N)."""
    style = _style(style, hyp, goal)
    aff = _affine_form(n, table)
    if aff is not None and (style == STANDALONE or n > MAX_FINOPTABLE_N):
        return false_affine_code(n, *aff, hyp, goal, style=style)
    return false_table_code(n, table, hyp, goal, style=style)


def _residue_affine_text(a, b, c):
    parts = []
    if a == 1:
        parts.append("a")
    elif a:
        parts.append(f"{a} * a")
    if b == 1:
        parts.append("b")
    elif b:
        parts.append(f"{b} * b")
    if c > 0:
        parts.append(str(c))
    expr = " + ".join(parts) if parts else "0"
    if c < 0 and parts:
        expr = f"{expr} - {-c}"
    return expr


def _residue_op_text(m, A, B, C):
    def branch(r):
        leaves = [_residue_affine_text(A[r][t], B[r][t], C[r][t]) for t in range(m)]
        out = leaves[m - 1]
        for t in range(m - 2, -1, -1):
            out = f"if b % {m} = {t} then {leaves[t]} else ({out})"
        return out
    out = branch(m - 1)
    for r in range(m - 2, -1, -1):
        out = f"if a % {m} = {r} then ({branch(r)}) else ({out})"
    return out


def _term_op_text(t: Term) -> str:
    if isinstance(t, str):
        return t
    l = t[0] if isinstance(t[0], str) else f"({_term_op_text(t[0])})"
    r = t[1] if isinstance(t[1], str) else f"({_term_op_text(t[1])})"
    return f"submission.op {l} {r}"


def false_nat_residue_code(hyp: Equation, m: int, A, B, C, witness, goal: Equation | None = None, *,
                           style: str | None = None) -> str:
    """Infinite countermodel on ℕ: op(x, y) = A[r][s]·x + B[r][s]·y + C[r][s]
    (truncated) with r = x mod m, s = y mod m. Law by
    ``simp only [submission.op]; grind``, refutation by a witness and
    ``decide`` — the shape that settled the Austin pair E1167 ⇒ E1763."""
    style = _style(style, hyp, goal)
    show = f"{_term_op_text(hyp.lhs)} = {_term_op_text(hyp.rhs)}"
    wit = " ".join(str(v) for v in witness)
    params = f"-- model: porc m={m} A={A} B={B} C={C} witness={list(witness)}"
    header = "import JudgeProblem\n" if style == JUDGE else prelude(hyp, goal, "false")
    decl = "def" if style == JUDGE else "theorem"
    return (f"{header}{params}\n\n"
            f"def submission.op (a b : Nat) : Nat :=\n  {_residue_op_text(m, A, B, C)}\n\n"
            "def submission.inst : Magma Nat := { op := submission.op }\n\n"
            "theorem submission.lhs : @EquationLHS Nat submission.inst := by\n"
            f"  intro {' '.join(hyp.variables)}\n  show {show}\n  simp only [submission.op]\n  grind\n\n"
            "theorem submission.rhs : ¬ @EquationRHS Nat submission.inst := by\n"
            f"  intro h\n  have := h {wit}\n  revert this; decide\n\n"
            f"{decl} submission : Goal :=\n  ⟨Nat, submission.inst, submission.lhs, submission.rhs⟩\n")


def superposition_code(hyp: Equation, goal: Equation, proof, *, style: str | None = None) -> str | None:
    """Certificate for a goal reached by superposition (a
    :class:`~eqtheory.completion.SuperpositionProof`)."""
    lem_lines = lemma_haves(hyp, proof.derived, {proof.lemma["name"]})
    if lem_lines is None:
        return None
    args = " ".join(render_term(a) for a in proof.args)
    expr = f"{proof.lemma['name']} {args}".strip()
    if proof.flipped:
        expr = f"({expr}).symm"
    intro = f"intro {' '.join(goal.variables)}\n" if goal.variables else ""
    return true_code(f"{intro}{''.join(ln + chr(10) for ln in lem_lines)}exact {expr}", hyp, goal, style=style)


def seeded_grind_bodies(hyp: Equation, goal: Equation, seeds) -> list[tuple[str, str]]:
    """Tactic bodies ``intro …; have lemK …; grind`` from
    :func:`~eqtheory.completion.seed_lemmas` output."""
    head = [f"intro {' '.join(goal.variables)}"] if goal.variables else []
    out = []
    for label, seed, derived in seeds:
        lines = lemma_haves(hyp, derived, {lem["name"] for lem in seed})
        if lines is None:
            continue
        body = "\n".join(head + lines + ["grind"])
        if all(body != b for _, b in out):
            out.append((f"seeded-grind({label})", body))
    return out


def egraph_proof_code(hyp: Equation, goal: Equation, lemmas: list, chain: Chain, derived=(), *,
                      style: str | None = None) -> str | None:
    """Certificate for an e-graph proof of the goal (shared sub-proofs as
    ``have``s; derived lemmas used by the chain emitted first)."""
    rules = {lem["name"]: (lem["lhs"], lem["rhs"], tuple(lem["vars"])) for lem in derived}
    used = _used_names(lemmas, chain)
    if not chain and not lemmas:
        body = f"intro {' '.join(goal.variables)}\nrfl" if goal.variables else "rfl"
        return true_code(body, hyp, goal, style=style)
    lem_lines = lemma_haves(hyp, derived, used) if used else []
    if lem_lines is None:
        return None
    lines, expr, end = shared_proof_lines(hyp, lemmas, chain, goal.lhs, rules)
    if expr is None or end != goal.rhs:
        return None
    have_block = "".join(ln + "\n" for ln in lem_lines + lines)
    return true_code(f"intro {' '.join(goal.variables)}\n{have_block}exact {expr}", hyp, goal, style=style)
