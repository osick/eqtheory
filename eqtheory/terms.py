"""Terms, equations and the basic operations on them.

A *term* over a magma is a variable (a one-letter string) or a pair
``(left, right)`` standing for ``left ◇ right``. This tuple encoding is
deliberately minimal: it hashes, compares and pickles for free, and every
algorithm in the library — matching, unification, rewriting, the
Knuth–Bendix order, e-graph construction — is a few lines of structural
recursion over it.

An *equation* ``l = r`` is read universally over all its variables. A
*problem* is a pair of equations (hypothesis, goal) and asks whether every
magma satisfying the hypothesis satisfies the goal.

Design notes
------------
* The operator may be written ``◇`` (U+25C7) or ``*``; ``normalize`` maps
  ``*`` to ``◇`` and every parser calls it, so both spellings work
  everywhere.
* ``match`` is one-way (pattern variables bind, term variables are rigid);
  ``unify`` is two-way with an occurs check. Keeping them apart is a
  soundness matter, not a convenience: a proof may instantiate a lemma to
  fit a goal, never the goal to fit the lemma.
* ``kbo_greater`` is the ground Knuth–Bendix order specialised to a
  signature with one binary symbol and unit weights: the weight of a term
  is its leaf count, ties are broken lexicographically over the children,
  distinct variables are incomparable. It is a strict order, stable under
  context, and well founded along any rewrite sequence (the variable
  universe never grows and the weight never increases).
"""
from __future__ import annotations

import itertools
import re
from dataclasses import dataclass
from typing import Callable, Iterator, Mapping, Union

OP = "◇"
Term = Union[str, tuple]          # str = variable, tuple = (left, right)
Subst = dict[str, Term]
_VAR_RE = re.compile(r"\b([a-z])\b")


# ── text ↔ terms ─────────────────────────────────────────────────────────

def normalize(text: str) -> str:
    """Canonicalise the operator spelling: ``*`` → ``◇``."""
    return text.replace("*", OP)


def _strip_outer_parens(s: str) -> str:
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth, matched = 0, True
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            if depth == 0 and i < len(s) - 1:
                matched = False
                break
        if not matched:
            break
        s = s[1:-1].strip()
    return s


def parse_term(text: str) -> Term:
    """Parse ``"(x ◇ y) ◇ z"`` into ``(("x", "y"), "z")``.

    The operator is left-associative; parentheses group. Raises
    ``ValueError`` on anything that is not a term over one-letter
    variables.
    """
    s = _strip_outer_parens(normalize(text))
    depth, last_op = 0, -1
    for i, c in enumerate(s):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif c == OP and depth == 0:
            last_op = i
    if last_op >= 0:
        return (parse_term(s[:last_op]), parse_term(s[last_op + 1:]))
    if re.fullmatch(r"[a-z]", s):
        return s
    raise ValueError(f"cannot parse term: {s!r}")


def render_term(term: Term, op: str = OP) -> str:
    """Fully parenthesised rendering, the form Lean and the judge use."""
    if isinstance(term, str):
        return term
    return f"({render_term(term[0], op)} {op} {render_term(term[1], op)})"


def _var_order(text: str) -> list[str]:
    seen: list[str] = []
    for v in _VAR_RE.findall(text):
        if v not in seen:
            seen.append(v)
    return seen


@dataclass(frozen=True)
class Equation:
    """A universally quantified equation ``lhs = rhs``.

    ``variables`` are in first-appearance order — the binder order Lean's
    ``∀`` uses in the judge's problem module, which matters when a
    certificate instantiates a hypothesis positionally.
    """
    lhs: Term
    rhs: Term
    variables: tuple[str, ...]

    @property
    def text(self) -> str:
        return f"{render_term(self.lhs)} = {render_term(self.rhs)}"

    def evaluate(self, op: Callable[[int, int], int], env: Mapping[str, int]) -> bool:
        return evaluate(self.lhs, op, env) == evaluate(self.rhs, op, env)


def parse_equation(text: str) -> Equation:
    """Parse ``"x = y ◇ (x ◇ z)"`` into an :class:`Equation`."""
    text = normalize(text)
    if "=" not in text:
        raise ValueError(f"not an equation: {text!r}")
    l, r = text.split("=", 1)
    return Equation(parse_term(l), parse_term(r), tuple(_var_order(text)))


@dataclass(frozen=True)
class Problem:
    """Does ``hypothesis`` imply ``goal`` in every magma?"""
    hypothesis: Equation
    goal: Equation

    @classmethod
    def parse(cls, hypothesis: str, goal: str) -> "Problem":
        return cls(parse_equation(hypothesis), parse_equation(goal))


# ── structural operations ────────────────────────────────────────────────

def term_vars(t: Term, acc: list[str] | None = None) -> list[str]:
    """Variables of ``t`` in first-appearance order."""
    if acc is None:
        acc = []
    if isinstance(t, str):
        if t not in acc:
            acc.append(t)
    else:
        term_vars(t[0], acc)
        term_vars(t[1], acc)
    return acc


def term_leaves(t: Term) -> int:
    """Number of variable occurrences — the KBO weight with unit weights."""
    return 1 if isinstance(t, str) else term_leaves(t[0]) + term_leaves(t[1])


def positions(t: Term, path: tuple[int, ...] = ()) -> Iterator[tuple[tuple[int, ...], Term]]:
    """All (path, subterm) pairs, root first (pre-order)."""
    yield path, t
    if not isinstance(t, str):
        yield from positions(t[0], path + (0,))
        yield from positions(t[1], path + (1,))


def subterm(t: Term, path: tuple[int, ...]) -> Term:
    for i in path:
        t = t[i]
    return t


def replace_at(t: Term, path: tuple[int, ...], new: Term) -> Term:
    """``t`` with the subterm at ``path`` replaced by ``new``."""
    if not path:
        return new
    l, r = t
    if path[0] == 0:
        return (replace_at(l, path[1:], new), r)
    return (l, replace_at(r, path[1:], new))


def substitute(t: Term, sub: Mapping[str, Term]) -> Term:
    """Apply a substitution; variables outside ``sub`` stay free."""
    if isinstance(t, str):
        return sub.get(t, t)
    return (substitute(t[0], sub), substitute(t[1], sub))


def rename(t: Term, mapping: Mapping[str, str]) -> Term:
    """Rename variables (a substitution restricted to variables)."""
    return substitute(t, mapping)


def evaluate(t: Term, op: Callable[[int, int], int], env: Mapping[str, int]) -> int:
    """Value of ``t`` under an operation and a variable assignment."""
    if isinstance(t, str):
        return env[t]
    return op(evaluate(t[0], op, env), evaluate(t[1], op, env))


def holds(eq: Equation, op: Callable[[int, int], int], carrier: range | int) -> bool:
    """Does ``eq`` hold for *every* assignment over the carrier?

    ``carrier`` is ``range(n)`` (or ``n``) — the finite case — or any
    finite sample of an infinite carrier, in which case the answer is only
    necessary evidence, never a proof.
    """
    rng = range(carrier) if isinstance(carrier, int) else carrier
    for vals in itertools.product(rng, repeat=len(eq.variables)):
        env = dict(zip(eq.variables, vals))
        if evaluate(eq.lhs, op, env) != evaluate(eq.rhs, op, env):
            return False
    return True


# ── matching and unification ─────────────────────────────────────────────

def match(pattern: Term, term: Term, sub: Subst | None = None) -> Subst | None:
    """One-way match: bind ``pattern``'s variables to subterms of ``term``.

    Deliberately *not* unification — the variables of ``term`` are rigid.
    Returns the extended substitution, or ``None``.
    """
    if sub is None:
        sub = {}
    if isinstance(pattern, str):
        if pattern in sub:
            return sub if sub[pattern] == term else None
        out = dict(sub)
        out[pattern] = term
        return out
    if isinstance(term, str):
        return None
    sub = match(pattern[0], term[0], sub)
    if sub is None:
        return None
    return match(pattern[1], term[1], sub)


def _walk(t: Term, sub: Mapping[str, Term]) -> Term:
    while isinstance(t, str) and t in sub:
        t = sub[t]
    return t


def _occurs(v: str, t: Term, sub: Mapping[str, Term]) -> bool:
    t = _walk(t, sub)
    if isinstance(t, str):
        return t == v
    return _occurs(v, t[0], sub) or _occurs(v, t[1], sub)


def unify(t1: Term, t2: Term, sub: Subst | None = None) -> Subst | None:
    """Syntactic unification with occurs check (variables shared).

    Returns a triangular substitution; use :func:`resolve` to apply it.
    """
    if sub is None:
        sub = {}
    t1, t2 = _walk(t1, sub), _walk(t2, sub)
    if t1 == t2:
        return sub
    if isinstance(t1, str):
        if _occurs(t1, t2, sub):
            return None
        out = dict(sub)
        out[t1] = t2
        return out
    if isinstance(t2, str):
        return unify(t2, t1, sub)
    sub = unify(t1[0], t2[0], sub)
    if sub is None:
        return None
    return unify(t1[1], t2[1], sub)


def resolve(t: Term, sub: Mapping[str, Term]) -> Term:
    """Apply a (possibly triangular) unifier, chasing variable chains."""
    t = _walk(t, sub)
    if isinstance(t, str):
        return t
    return (resolve(t[0], sub), resolve(t[1], sub))


# ── the reduction order ──────────────────────────────────────────────────

def kbo_greater(s: Term, t: Term) -> bool:
    """Ground Knuth–Bendix order: is ``s`` strictly greater than ``t``?

    Weight = leaf count (one binary symbol, unit weights); on a weight tie
    the children are compared lexicographically, left first; two distinct
    variables are incomparable; nothing is greater than itself.
    """
    ws, wt = term_leaves(s), term_leaves(t)
    if ws != wt:
        return ws > wt
    if isinstance(s, str) or isinstance(t, str):
        return False
    if s[0] != t[0]:
        return kbo_greater(s[0], t[0])
    return kbo_greater(s[1], t[1])
