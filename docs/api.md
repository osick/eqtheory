# API overview

| module | main entry points |
|---|---|
| `eqtheory.terms` | `parse_term`, `render_term`, `parse_equation`, `Equation`, `Problem`, `term_vars`, `positions`, `subterm`, `replace_at`, `substitute`, `rename`, `match`, `unify`, `resolve`, `kbo_greater`, `evaluate`, `holds` |
| `eqtheory.proofs` | chain links (`h`/`lem`/`ref`/`cong`), `invert`, `wrap_cong`, `rule_link`, `replay`, `validate` |
| `eqtheory.egraph` | `EGraph` (`add_term`, `union`, `rebuild`, `ematch`, `explain`, `to_dot`, `render`), `saturate`, `prove_goal`, `prove_singleton` |
| `eqtheory.completion` | `Budget`, `derive_lemmas`, `rewrite_step`, `interreduce`, `overlap_pairs`, `push_overlap`, `goal_instance`, `prove_by_superposition`, `DEFAULT_LADDER`, `DEEP_LADDER`, `seed_lemmas` |
| `eqtheory.models.finite` | `Countermodel`, `SearchFacts`, `scan`, `linear_countermodel`, `structured_tables`, `find_model_cells`, `SatSolver`, `sat_encode`, `find_model_sat`, `decide_size`, `find_countermodel`, `is_countermodel` |
| `eqtheory.models.infinite` | `NatResidueModel`, `residue_affine_countermodel` |
| `eqtheory.lean.certs` | `true_code`, `false_code`, `false_table_code`, `false_affine_code`, `false_nat_residue_code`, `superposition_code`, `egraph_proof_code`, `seeded_grind_bodies`, `lemma_haves`, `render_chain` |
| `eqtheory.lean.check` | `configure`, `LeanConfig`, `problem_module`, `compile_certificate`, `make_judge` |
| `eqtheory.llm` | `DEFAULT_PROMPT`, `load_prompt`, `render_prompt`, `format_search_facts`, `extract_json`, `clean_proof_body`, `preflight`, `OpenRouterClient`, `llm_stage` |
| `eqtheory.solve` | `Config`, `Trace`, `Answer`, `stage_*`, `solve` |
| `eqtheory.viz` | `egraph_to_dot`, `render_egraph`, `chain_to_dot` |
| `eqtheory.cli` | `eqtheory solve / prove / model / egraph / viz-proof / cert` |

Docstrings carry the details; `python -c "import eqtheory.completion as m; help(m)"`.
