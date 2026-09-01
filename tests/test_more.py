"""Coverage of the CLI (in-process), the Lean check helpers, the LLM
client transport, the SVG fallback and the remaining model-finder paths."""
import io
import json
import time
import urllib.request

import pytest

from eqtheory import Problem, cli, viz
from eqtheory.egraph import prove_goal
from eqtheory.lean import check as lean_check
from eqtheory import llm as llm_mod
from eqtheory.models import finite
from eqtheory.proofs import replay, validate

FALSE = Problem.parse("x ◇ y = y ◇ x", "x = x ◇ x")
EQSAT = Problem.parse("x = x ◇ y", "x = (x ◇ y) ◇ z")
ORDER5_A = Problem.parse("x = (y ◇ (z ◇ (z ◇ (x ◇ z)))) ◇ z", "x = (x ◇ y) ◇ (((z ◇ z) ◇ z) ◇ z)")
AUSTIN = Problem.parse("x = y ◇ ((z ◇ (y ◇ y)) ◇ x)", "x = (y ◇ z) ◇ ((x ◇ z) ◇ x)")


class TestCLI:
    def test_solve_text_and_json(self, capsys, tmp_path):
        cli.main(["solve", "--model-budget", "5", "--out", str(tmp_path / "c.lean"), FALSE.hypothesis.text, FALSE.goal.text])
        out = capsys.readouterr().out
        assert "verdict: false" in out and (tmp_path / "c.lean").read_text().startswith("import JudgeProblem")
        cli.main(["solve", "--json", "--model-budget", "5", EQSAT.hypothesis.text, EQSAT.goal.text])
        assert json.loads(capsys.readouterr().out)["verdict"] == "true"

    def test_model_prove_cert_viz(self, capsys, tmp_path):
        cli.main(["model", "--budget", "10", "--cert", FALSE.hypothesis.text, FALSE.goal.text])
        assert "countermodel on Fin" in capsys.readouterr().out
        cli.main(["model", "--budget", "5", "--infinite", "--cert", AUSTIN.hypothesis.text, AUSTIN.goal.text])
        assert "ℕ model" in capsys.readouterr().out
        cli.main(["prove", "--budget", "60", ORDER5_A.hypothesis.text, ORDER5_A.goal.text])
        assert "proved by" in capsys.readouterr().out
        cli.main(["prove", "--budget", "2", FALSE.hypothesis.text, FALSE.goal.text])
        assert "no superposition proof" in capsys.readouterr().out
        cli.main(["cert", "--table", "[[0,0],[1,1]]", "x = x", "x = y"])
        assert "finOpTable" in capsys.readouterr().out
        with pytest.raises(SystemExit):
            cli.main(["cert", "--table", "[[0,0],[0,0]]", "x = x", "x = x"])
        body = tmp_path / "body.txt"; body.write_text("intro x\nrfl")
        cli.main(["cert", "--proof", str(body), "x = x", "x = x"])
        assert "rfl" in capsys.readouterr().out
        out = tmp_path / "p.dot"
        cli.main(["viz-proof", "--out", str(out), "--budget", "3", EQSAT.hypothesis.text, EQSAT.goal.text])
        assert out.exists()
        dot = tmp_path / "e.dot"
        cli.main(["egraph", "--dot", str(dot), "--lemmas", "--budget", "2", EQSAT.hypothesis.text, EQSAT.goal.text])
        assert "digraph" in dot.read_text()

    def test_lean_flag_without_config(self, monkeypatch):
        monkeypatch.setattr(lean_check, "configure", lambda **kw: None)
        with pytest.raises(SystemExit):
            cli.main(["solve", "--lean", "x = x", "x = x"])


class TestLeanCheck:
    def test_problem_module_shapes(self):
        t = lean_check.problem_module(FALSE.hypothesis, FALSE.goal, "true")
        f = lean_check.problem_module(FALSE.hypothesis, FALSE.goal, "false")
        assert "EquationLHS G → EquationRHS G" in t and "¬ EquationRHS G" in f and "∀ (x : G) (y : G)" in t

    def test_configure_and_lean_path(self, tmp_path, monkeypatch):
        for k in ("EQTHEORY_LEAN_BIN", "EQTHEORY_JUDGE_ROOT", "EQTHEORY_LEAN_PATH"):
            monkeypatch.delenv(k, raising=False)
        monkeypatch.setattr(lean_check.shutil, "which", lambda name: None)
        assert lean_check.configure() is None
        (tmp_path / ".lake/packages/mathlib/.lake/build/lib/lean").mkdir(parents=True)
        lp = lean_check.lean_path_for(tmp_path)
        assert "packages/mathlib" in lp and lp.startswith(str(tmp_path))

    def test_compile_with_fake_lean(self, tmp_path):
        fake = tmp_path / "lean"
        fake.write_text("#!/bin/sh\necho ok\n"); fake.chmod(0o755)
        cfg = lean_check.LeanConfig(str(fake), "/nonexistent", 5)
        res = lean_check.compile_certificate(FALSE.hypothesis, FALSE.goal, "false", "def submission : Goal := sorry",
                                             cfg, workdir=str(tmp_path / "w"))
        assert res.ok and (tmp_path / "w" / "Submission.lean").exists()
        assert lean_check.make_judge(FALSE.hypothesis, FALSE.goal, cfg)("false", "x")


class TestLLMClient:
    def test_openrouter_transport(self, monkeypatch):
        seen = {}

        class Resp(io.BytesIO):
            def __enter__(self): return self
            def __exit__(self, *a): return False

        def fake_urlopen(req, timeout=None):
            seen["payload"] = json.loads(req.data); seen["auth"] = req.get_header("Authorization")
            body = {"choices": [{"message": {"content": "", "reasoning": '{"verdict":"true","proof":"grind"}'},
                                 "finish_reason": "length"}], "usage": {"prompt_tokens": 10, "completion_tokens": 5}}
            return Resp(json.dumps(body).encode())
        monkeypatch.setattr(urllib.request, "urlopen", fake_urlopen)
        c = llm_mod.OpenRouterClient(api_key="k", reasoning_effort="low", provider_order="deepinfra/bf16", seed=7)
        assert "verdict" in c("hi") and c.calls == 1 and c.tokens == {"input": 10, "output": 5}
        assert seen["payload"]["seed"] == 7 and seen["payload"]["reasoning"] == {"effort": "low"}
        assert seen["payload"]["provider"] == {"order": ["deepinfra/bf16"]} and seen["auth"] == "Bearer k"

    def test_missing_key_and_retry_exhaustion(self, monkeypatch):
        monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
        with pytest.raises(RuntimeError):
            llm_mod.OpenRouterClient()("x")

        def boom(req, timeout=None):
            raise OSError("down")
        monkeypatch.setattr(urllib.request, "urlopen", boom)
        monkeypatch.setattr(llm_mod.time, "sleep", lambda s: None)
        with pytest.raises(RuntimeError):
            llm_mod.OpenRouterClient(api_key="k")("x")

    def test_stage_handles_bad_rounds(self):
        answers = iter(["garbage", '{"verdict":"maybe"}', '{"verdict":"true","proof":""}',
                        '{"verdict":"true","proof":"intro x\\nsorry"}', '{"verdict":"false"}',
                        '{"verdict":"false","affine":{"n":1}}', '{"verdict":"false","counterexample_table":[[0,5]]}',
                        '{"verdict":"true","proof":"intro x\\ngrind"}', '{"verdict":"true","proof":"intro x\\ngrind"}'])
        out = llm_mod.llm_stage(FALSE, lambda p: next(answers), judge=lambda v, c: False, max_rounds=9)
        assert out.verdict is None and len(out.attempts) == 9 and any("IDENTICAL" in a for a in out.attempts)
        assert llm_mod.load_prompt.__doc__
        with pytest.raises(ValueError):
            llm_mod.load_prompt(__file__)


class TestVizAndProofs:
    def test_svg_fallback_and_dot(self, tmp_path, monkeypatch):
        eg, l, r = prove_goal(EQSAT.hypothesis, EQSAT.goal, time_budget=3)
        monkeypatch.setattr(viz.shutil, "which", lambda name: None)
        kind = viz.render_egraph(eg, str(tmp_path / "e.svg"), highlight=(l, r), proof_pairs=((l, r),), max_classes=50)
        assert kind in ("svg-fallback", "dot") and (tmp_path / "e.svg").exists()
        lemmas, chain = eg.explain(l, r)
        assert "digraph" in viz.chain_to_dot(lemmas, chain)

    def test_replay_rejects_bad_chains(self):
        hyp = (EQSAT.hypothesis.lhs, EQSAT.hypothesis.rhs, list(EQSAT.hypothesis.variables))
        assert not validate(hyp, [], [("h", ("x", "y"), True)], "x", "y", {})
        assert not validate(hyp, [], [("lem", "nope", ("x",), True)], "x", "y", {})
        assert not validate(hyp, [], [("ref", "e9", False)], "x", "y", {})
        with pytest.raises(Exception):
            replay([("cong", [("h", ("x", "y"), True)], [])], "x", hyp, {}, {})


class TestModelsMore:
    def test_matrix_linear_sweep_and_structured_zoo(self):
        cm = finite._matrix_linear_sweep(FALSE.hypothesis, FALSE.goal, (2,), time.monotonic() + 30)
        assert cm is not None and cm.n == 4 and finite.is_countermodel(FALSE.hypothesis, FALSE.goal, 4, cm.table)
        assert len(list(finite.structured_tables(5))) > 500 and len(list(finite.structured_tables(6))) > 300

    def test_sat_and_cells_agree_on_unsat(self):
        h, g = ORDER5_A.hypothesis, ORDER5_A.goal
        assert finite.find_model_sat(h, g, 4, time.monotonic() + 60) == (None, True)
        assert finite.find_model_cells(h, g, 3, time.monotonic() + 60) == (None, True)
        assert finite.decide_size(h, g, 3, time.monotonic() + 60, memory_mb=0.001)[1]   # forced onto the cell search

    def test_deadline_paths(self):
        h, g = ORDER5_A.hypothesis, ORDER5_A.goal
        assert finite.find_model_cells(h, g, 7, time.monotonic() - 1) == (None, False)
        assert finite.find_model_sat(h, g, 6, time.monotonic() - 1) in ((None, False), (None, True))
        assert finite.find_countermodel(h, g, time_budget=0.0) is None
        assert finite.linear_countermodel(h, g, time_budget=0.0) is None
