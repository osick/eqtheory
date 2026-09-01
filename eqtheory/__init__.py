"""eqtheory — equational theories over magmas.

Term rewriting with a Knuth–Bendix order, proof-producing e-graph
saturation, goal-directed superposition, finite and infinite countermodel
search, and Lean 4 certificate generation. The algorithms of the SAIR
Stage-2 solver (2026) as a library; no lookup tables, no stored proofs —
everything is derived from the two equations of a problem at runtime.
"""
from .terms import (  # noqa: F401
    Equation, Problem, Term, OP,
    parse_term, render_term, parse_equation, normalize,
    term_vars, term_leaves, positions, subterm, replace_at,
    match, unify, substitute, rename,
    kbo_greater, holds, evaluate,
)

__version__ = "0.1.0"

from .solve import solve, Answer, Config, Trace  # noqa: E402,F401
from .completion import derive_lemmas, prove_by_superposition, Budget  # noqa: E402,F401
from .egraph import EGraph, saturate, prove_goal, prove_singleton  # noqa: E402,F401
from .models import find_countermodel, residue_affine_countermodel, Countermodel, NatResidueModel  # noqa: E402,F401

__all__ = [
    "Equation", "Problem", "Term", "OP", "parse_term", "render_term", "parse_equation", "normalize",
    "term_vars", "term_leaves", "positions", "subterm", "replace_at", "match", "unify", "substitute", "rename",
    "kbo_greater", "holds", "evaluate",
    "solve", "Answer", "Config", "Trace", "derive_lemmas", "prove_by_superposition", "Budget",
    "EGraph", "saturate", "prove_goal", "prove_singleton",
    "find_countermodel", "residue_affine_countermodel", "Countermodel", "NatResidueModel", "__version__",
]
