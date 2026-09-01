"""Lean 4 certificate text (``certs``) and an optional compile check (``check``)."""
from .certs import (  # noqa: F401
    render_chain, lemma_haves, shared_proof_lines, true_code, false_code,
    false_table_code, false_affine_code, false_nat_residue_code,
    superposition_code, seeded_grind_bodies, egraph_proof_code,
    MAX_FINOPTABLE_N, MAX_REC_DEPTH,
)
from .check import LeanConfig, CheckResult, configure, compile_certificate, make_judge, problem_module  # noqa: F401

__all__ = ['CheckResult', 'LeanConfig', 'compile_certificate', 'configure', 'make_judge', 'problem_module']

__all__ = [
    "render_chain",
    "lemma_haves",
    "shared_proof_lines",
    "true_code",
    "false_code",
    "false_table_code",
    "false_affine_code",
    "false_nat_residue_code",
    "superposition_code",
    "seeded_grind_bodies",
    "egraph_proof_code",
    "MAX_FINOPTABLE_N",
    "MAX_REC_DEPTH",
    "LeanConfig",
    "CheckResult",
    "configure",
    "compile_certificate",
    "make_judge",
    "problem_module",
]
