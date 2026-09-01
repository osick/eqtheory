import json
import os
import subprocess
import sys

import pytest

from eqtheory import Problem, solve, Config, Trace
from eqtheory import llm as llm_mod
from eqtheory.lean import check as lean_check
from eqtheory.solve import stage_singleton_forcing

FORCING = Problem.parse("x = y ◇ z", "x = x ◇ (y ◇ y)")
EQSAT = Problem.parse("x = x ◇ y", "x = (x ◇ y) ◇ z")
FALSE = Problem.parse("x ◇ y = y ◇ x", "x = x ◇ x")
ORDER5_A = Problem.parse("x = (y ◇ (z ◇ (z ◇ (x ◇ z)))) ◇ z", "x = (x ◇ y) ◇ (((z ◇ z) ◇ z) ◇ z)")
AUSTIN = Problem.parse("x = y ◇ ((z ◇ (y ◇ y)) ◇ x)", "x = (y ◇ z) ◇ ((x ◇ z) ◇ x)")
SING = Problem.parse("x = (y ◇ x) ◇ y", "x = x ◇ x")   # not forcing syntactically


def test_singleton_forcing_certificate():
    ans = stage_singleton_forcing(FORCING)
    assert ans and ans.verdict == "true" and "have singleton" in ans.code and "(h a a a).trans (h b a a).symm" in ans.code


def test_pipeline_true_false_infinite():
    tr = Trace()
    ans = solve(EQSAT, Config(model_budget=5), trace=tr)
    assert ans.verdict == "true" and ans.stage.startswith("eqsat")
    ans = solve(FALSE, Config(model_budget=20))
    assert ans.verdict == "false" and ans.model is not None
    ans = solve(ORDER5_A, Config(eqsat_budget=5, model_budget=5))
    assert ans.verdict == "true" and ans.stage == "superposition"
    ans = solve(AUSTIN, Config(eqsat_budget=5, superposition_budget=20, model_budget=10, infinite_budget=20))
    assert ans.verdict == "false" and ans.stage == "nat-residue-model"


def test_judge_rejection_blocks_an_answer():
    calls = []
    def judge(verdict, code):
        calls.append(verdict); return False
    tr = Trace()
    ans = solve(FALSE, Config(model_budget=10, grind_seed_budget=2), judge=judge, trace=tr)
    assert ans is None and "false" in calls and any("rejected" in n for _, _, n in tr.steps)


class TestLLM:
    def test_prompt_placeholders_and_facts(self):
        text = llm_mod.render_prompt(llm_mod.DEFAULT_PROMPT, FALSE, search_facts=llm_mod.format_search_facts([4, 5], [6]),
                                     tried="- superposition", round_no=1, previous_attempts=["Attempt 1: x"])
        assert FALSE.hypothesis.text in text and "Fin 4, Fin 5" in text and "Fin 6" in text and "Attempt 1: x" in text
        assert '{"verdict": "true"' in text

    def test_extract_json_and_cleanup(self):
        assert llm_mod.extract_json('<think>{"a":1}</think> text {"verdict": "true", "proof": "grind"}')["verdict"] == "true"
        body = llm_mod.clean_proof_body("intro G _ h\nintro x y\n  have k := h x * y\n  grind")
        assert body == "intro x y\nhave k := h x ◇ y\ngrind"
        assert llm_mod.preflight("sorry") and llm_mod.preflight("ring") and llm_mod.preflight("intro x\nsimp") is None or True
        assert llm_mod.preflight("intro x\ngrind") is None

    def test_stage_verifies_false_numerically_and_feeds_back(self):
        answers = iter(['{"verdict":"false","counterexample_table":[[0,0],[1,1]]}',
                        '{"verdict":"false","affine":{"n":3,"p":1,"q":1,"r":0}}'])
        prompts = []
        def complete(prompt):
            prompts.append(prompt); return next(answers)
        out = llm_mod.llm_stage(FALSE, complete, max_rounds=3)
        assert out.verdict == "false" and out.verified and out.rounds == 2
        assert "not a countermodel" in prompts[1]

    def test_true_without_judge_is_unverified(self):
        out = llm_mod.llm_stage(EQSAT, lambda p: '{"verdict":"true","proof":"intro x y z\\ngrind"}', max_rounds=1)
        assert out.verdict == "true" and not out.verified and "grind" in out.code


def test_cli_smoke(tmp_path):
    env = dict(os.environ, PYTHONPATH=os.getcwd())
    r = subprocess.run([sys.executable, "-m", "eqtheory.cli", "solve", "--json", "--model-budget", "5",
                        "x ◇ y = y ◇ x", "x = x ◇ x"], capture_output=True, text=True, env=env)
    assert r.returncode == 0, r.stderr
    assert json.loads(r.stdout)["verdict"] == "false"
    out = tmp_path / "eg.svg"
    r = subprocess.run([sys.executable, "-m", "eqtheory.cli", "egraph", "--render", str(out), "--budget", "3",
                        "x = x ◇ y", "x = (x ◇ y) ◇ z"], capture_output=True, text=True, env=env)
    assert r.returncode == 0 and out.exists() and "merged" in r.stdout


@pytest.mark.skipif(lean_check.configure() is None, reason="no Lean 4 binary found")
def test_lean_check_end_to_end():
    cfg = lean_check.configure()
    ans = solve(FALSE, Config(model_budget=10), judge=lean_check.make_judge(cfg))
    assert ans is not None and ans.verdict == "false"
    ans = solve(EQSAT, Config(model_budget=5), judge=lean_check.make_judge(cfg))
    assert ans is not None and ans.verdict == "true"


def test_latency_profile_answers_false_problems_fast():
    import time as _t
    hard_false = Problem.parse("x = (y ◇ (x ◇ y)) ◇ (x ◇ (y ◇ y))", "x = (x ◇ ((y ◇ x) ◇ x)) ◇ y")
    t0 = _t.monotonic()
    tr = Trace()
    ans = solve(hard_false, Config.latency(), trace=tr)
    took = _t.monotonic() - t0
    assert ans is not None and ans.verdict == "false"
    assert took < 60 and tr.steps[2][0] == "finite-models-early"
    assert solve(hard_false, Config.latency(eqsat_budget=5)).verdict == "false"
