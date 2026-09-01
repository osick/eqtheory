import os

import pytest

from eqtheory import config as cfg_mod
from eqtheory.config import Settings, load, configure, settings
from eqtheory.lean import certs, check as lean_check
from eqtheory.terms import Problem

P = Problem.parse("x = x ◇ y", "x = (x ◇ y) ◇ z")


@pytest.fixture(autouse=True)
def restore():
    before = settings.as_dict()
    yield
    configure(**before)


def test_defaults_then_file_then_env(tmp_path):
    f = tmp_path / "eqtheory.toml"
    f.write_text('[eqtheory]\nlean_toolchain = "leanprover/lean4:v4.99.0"\nmodel_max_n = 14\nllm_reasoning_effort = "none"\n')
    s = load(f, env={})
    assert s.lean_toolchain == "leanprover/lean4:v4.99.0" and s.model_max_n == 14 and s.llm_reasoning_effort is None
    s = load(f, env={"EQTHEORY_MODEL_MAX_N": "9", "EQTHEORY_LEAN_TOOLCHAIN": "", "EQTHEORY_LEAN_TIMEOUT": "12.5"})
    assert s.model_max_n == 9 and s.lean_toolchain is None and s.lean_timeout == 12.5
    assert Settings().lean_toolchain is not None                      # the shipped default pins a toolchain
    bad = tmp_path / "bad.toml"; bad.write_text("nope = 1\n")
    with pytest.raises(ValueError):
        load(bad, env={})
    with pytest.raises(ValueError):
        configure(nonsense=1)


def test_settings_flow_into_certificates_and_lean_config(monkeypatch):
    configure(lean_toolchain="leanprover/lean4:v4.99.0", lean_max_rec_depth=777)
    code = certs.true_code("intro x y z\nrfl", P.hypothesis, P.goal)
    assert "generated for leanprover/lean4:v4.99.0" in code and "maxRecDepth 777" in code
    assert lean_check.search_paths()[0].endswith("leanprover--lean4---v4.99.0/bin/lean")
    lc = lean_check.LeanConfig("/bin/true")
    assert lc.toolchain == "leanprover/lean4:v4.99.0" and lc.timeout == settings.lean_timeout
    configure(lean_toolchain=None)
    assert "generated for" not in certs.true_code("rfl", P.hypothesis, P.goal)
    assert lean_check.LeanConfig("/bin/true").toolchain is None


def test_no_pin_means_no_toolchain_file(tmp_path):
    fake = tmp_path / "lean"; fake.write_text("#!/bin/sh\necho ok\n"); fake.chmod(0o755)
    lc = lean_check.LeanConfig(str(fake), toolchain=None)
    res = lean_check.compile_certificate(certs.prelude(P.hypothesis, P.goal, "true") + "theorem submission : Goal := sorry",
                                         lc, workdir=str(tmp_path / "w"))
    assert res.ok is not None and not (tmp_path / "w" / "lean-toolchain").exists()


def test_config_file_lookup_and_describe(tmp_path, monkeypatch):
    f = tmp_path / "c.toml"; f.write_text("model_max_n = 11\n")
    monkeypatch.setenv("EQTHEORY_CONFIG", str(f))
    assert cfg_mod.config_file() == f
    cfg_mod.reload()
    assert settings.model_max_n == 11
    text = cfg_mod.describe()
    assert "model_max_n" in text and str(f) in text
    monkeypatch.setenv("EQTHEORY_CONFIG", str(tmp_path / "missing.toml"))
    assert cfg_mod.config_file() is None or os.environ["EQTHEORY_CONFIG"]


def test_llm_client_and_solve_config_take_settings():
    from eqtheory.llm import OpenRouterClient
    from eqtheory.solve import Config
    configure(llm_model="acme/model-1", llm_api_key_env="ACME_KEY", llm_rounds=2, model_max_n=15)
    c = OpenRouterClient()
    assert c.model == "acme/model-1" and c.api_key_env == "ACME_KEY"
    with pytest.raises(RuntimeError, match="ACME_KEY"):
        c("x")
    assert Config().llm_rounds == 2 and Config().max_model_n == 15


def test_cli_config_command(capsys):
    from eqtheory import cli
    cli.main(["config"])
    out = capsys.readouterr().out
    assert "lean_toolchain" in out and "config file:" in out
