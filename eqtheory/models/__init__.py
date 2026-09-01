"""Countermodel search: finite magmas (tables) and infinite ones on ℕ."""
from .finite import (  # noqa: F401
    Countermodel, scan, is_countermodel, structured_tables, linear_countermodel,
    decide_size, find_model_cells, find_model_sat, find_countermodel, SearchFacts,
    MAX_TABLE_N,
)
from .infinite import NatResidueModel, residue_affine_countermodel  # noqa: F401

__all__ = ['NatResidueModel', 'residue_affine_countermodel']

__all__ = [
    "Countermodel",
    "scan",
    "is_countermodel",
    "structured_tables",
    "linear_countermodel",
    "decide_size",
    "find_model_cells",
    "find_model_sat",
    "find_countermodel",
    "SearchFacts",
    "MAX_TABLE_N",
    "NatResidueModel",
    "residue_affine_countermodel",
]
