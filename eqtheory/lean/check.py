"""Compile a certificate with Lean 4.

Standalone certificates (the default, see :mod:`eqtheory.lean.certs`)
need nothing but a Lean 4 toolchain: the file declares everything it
uses. :func:`configure` finds ``lean`` via ``EQTHEORY_LEAN_BIN``, the
``PATH`` or an elan installation; the check pins the validated toolchain
with a ``lean-toolchain`` file next to the certificate, so an elan proxy
selects (and, if necessary, downloads) exactly that version.

Judge-style certificates (``import JudgeProblem``) additionally need the
historical Stage-2 judge library on ``EQTHEORY_LEAN_PATH`` (or a built
checkout under ``EQTHEORY_JUDGE_ROOT``); they are compiled the way that
judge did, minus its policy checks.
"""
from __future__ import annotations

import glob
import os
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

from ..config import settings
from ..terms import Equation
from .certs import is_standalone, prelude

JUDGE_LINTER_FLAGS = ("-D", "linter.defProp=false")

def search_paths() -> list[str]:
    """Where a Lean binary is looked for after ``settings.lean_bin`` and the
    PATH: the elan toolchain matching ``settings.lean_toolchain``, then the
    elan proxy."""
    out = []
    tc = settings.lean_toolchain
    if tc:
        out.append(f"~/.elan/toolchains/{tc.replace('/', '--').replace(':', '---')}/bin/lean")
    out.append("~/.elan/bin/lean")
    return out


@dataclass
class LeanConfig:
    lean_bin: str
    lean_path: str | None = None      # only for judge-style certificates
    timeout: float = field(default_factory=lambda: settings.lean_timeout)
    toolchain: str | None = field(default_factory=lambda: settings.lean_toolchain)   # None = no pin


@dataclass
class CheckResult:
    ok: bool
    verdict: str
    seconds: float
    output: str


def find_lean() -> str | None:
    cands = [settings.lean_bin, shutil.which("lean")] + [os.path.expanduser(p) for p in search_paths()]
    for c in cands:
        if c and Path(c).exists():
            return c
    return None


def lean_path_for(judge_root: str | os.PathLike) -> str:
    """LEAN_PATH of a built judge checkout (own build dir + every package)."""
    root = Path(judge_root)
    entries = [str(root / ".lake" / "build" / "lib" / "lean")]
    entries += sorted(glob.glob(str(root / ".lake" / "packages" / "*" / ".lake" / "build" / "lib" / "lean")))
    return os.pathsep.join(entries)


def configure(lean_bin: str | None = None, judge_root: str | None = None, lean_path: str | None = None,
              timeout: float | None = None, toolchain: str | None = "unset") -> LeanConfig | None:
    """A configuration, or None when no Lean binary can be found. Defaults
    come from :mod:`eqtheory.config` (``lean_bin``, ``lean_timeout``,
    ``lean_toolchain``); ``judge_root``/``lean_path`` only matter for
    judge-style certificates (env ``EQTHEORY_JUDGE_ROOT``/``EQTHEORY_LEAN_PATH``)."""
    lean_bin = lean_bin or find_lean()
    if not lean_bin:
        return None
    lean_path = lean_path or os.environ.get("EQTHEORY_LEAN_PATH")
    judge_root = judge_root or os.environ.get("EQTHEORY_JUDGE_ROOT")
    if lean_path is None and judge_root:
        lean_path = lean_path_for(judge_root)
    cfg = LeanConfig(lean_bin, lean_path)
    if timeout is not None:
        cfg.timeout = timeout
    if toolchain != "unset":
        cfg.toolchain = toolchain
    return cfg


def _equation_def(name: str, eq: Equation) -> str:
    binders = " ".join(f"({v} : G)" for v in eq.variables)
    return f"@[reducible] def {name} (G : Type _) [Magma G] : Prop := ∀ {binders}, {eq.text}"


def problem_module(hyp: Equation, goal: Equation, verdict: str) -> str:
    """The judge-controlled ``JudgeProblem`` module (judge style only)."""
    target = ("∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G" if verdict == "true"
              else "∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G")
    return ("import JudgeMagma.Magma\n\n"
            f"{_equation_def('EquationLHS', hyp)}\n{_equation_def('EquationRHS', goal)}\n\n"
            f"abbrev Goal : Prop := {target}\n")


def verdict_of(code: str) -> str:
    """Which goal shape a standalone certificate proves."""
    for line in code.split("\n"):
        if line.startswith("abbrev Goal"):
            return "false" if "∃" in line else "true"
    return "true"


def compile_certificate(code: str, cfg: LeanConfig, workdir: str | None = None, *, hyp: Equation | None = None,
                        goal: Equation | None = None, verdict: str | None = None) -> CheckResult:
    """Compile one certificate. Standalone files need only ``cfg.lean_bin``;
    judge-style files need ``cfg.lean_path`` and the problem."""
    t0 = time.monotonic()
    tmp = Path(workdir or tempfile.mkdtemp(prefix="eqtheory-lean-"))
    tmp.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    try:
        if is_standalone(code):
            verdict = verdict or verdict_of(code)
            if cfg.toolchain:
                (tmp / "lean-toolchain").write_text(cfg.toolchain + "\n", encoding="utf-8")
            src = tmp / "Certificate.lean"
            src.write_text(code, encoding="utf-8")
            p = subprocess.run([cfg.lean_bin, str(src)], cwd=tmp, env=env, text=True, capture_output=True,
                               timeout=cfg.timeout)
        else:
            if cfg.lean_path is None or hyp is None or goal is None or verdict is None:
                return CheckResult(False, verdict or "?", 0.0,
                                   "judge-style certificate: needs the judge library (EQTHEORY_JUDGE_ROOT) and the problem")
            env["LEAN_PATH"] = os.pathsep.join([str(tmp), cfg.lean_path])
            src = tmp / "JudgeProblem.lean"
            src.write_text(problem_module(hyp, goal, verdict), encoding="utf-8")
            p = subprocess.run([cfg.lean_bin, f"--root={tmp}", "-o", str(tmp / "JudgeProblem.olean"), str(src)],
                               cwd=tmp, env=env, text=True, capture_output=True, timeout=cfg.timeout)
            if p.returncode != 0:
                return CheckResult(False, verdict, time.monotonic() - t0, "JudgeProblem: " + (p.stderr or p.stdout))
            sub = tmp / "Submission.lean"
            sub.write_text(code, encoding="utf-8")
            p = subprocess.run([cfg.lean_bin, *JUDGE_LINTER_FLAGS, f"--root={tmp}", str(sub)],
                               cwd=tmp, env=env, text=True, capture_output=True, timeout=cfg.timeout)
    except subprocess.TimeoutExpired:
        return CheckResult(False, verdict or "?", time.monotonic() - t0, "timeout")
    out = (p.stdout or "") + (p.stderr or "")
    ok = p.returncode == 0 and "error" not in out and "sorry" not in out
    return CheckResult(ok, verdict, time.monotonic() - t0, out)


def make_judge(cfg: LeanConfig, hyp: Equation | None = None, goal: Equation | None = None):
    """A ``judge(verdict, code) -> bool`` closure for :mod:`eqtheory.solve`."""
    return lambda verdict, code: compile_certificate(code, cfg, hyp=hyp, goal=goal, verdict=verdict).ok


__all__ = ["LeanConfig", "CheckResult", "search_paths", "find_lean", "lean_path_for", "configure",
           "problem_module", "verdict_of", "compile_certificate", "make_judge", "prelude"]
