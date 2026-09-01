"""Optional: compile a certificate against the Stage-2 judge library.

Needs a Lean 4 toolchain and a built checkout of the judge repository
(``equational-theories-lean-stage2`` — modules ``JudgeMagma``,
``JudgeDecide``, ``JudgeFinOp``, ``JudgeSupport`` built with ``lake``).
This is a *compile check*, not the competition judge: it does not apply
the declaration allowlist, the token scan or the nonce-named binding.
It exists so the library's certificates can be validated end to end.

Configuration, in order of precedence: explicit arguments,
``EQTHEORY_LEAN_BIN`` / ``EQTHEORY_JUDGE_ROOT`` / ``EQTHEORY_LEAN_PATH``.
"""
from __future__ import annotations

import glob
import os
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

from ..terms import Equation

LINTER_FLAGS = ("-D", "linter.defProp=false")   # Lean ≥ 4.32 default-on linter


@dataclass
class LeanConfig:
    lean_bin: str
    lean_path: str
    timeout: float = 300.0


@dataclass
class CheckResult:
    ok: bool
    verdict: str
    seconds: float
    output: str


def lean_path_for(judge_root: str | os.PathLike) -> str:
    """LEAN_PATH from a built judge checkout: its own build dir plus every
    package under ``.lake/packages`` (Mathlib, Batteries, …)."""
    root = Path(judge_root)
    entries = [str(root / ".lake" / "build" / "lib" / "lean")]
    entries += sorted(glob.glob(str(root / ".lake" / "packages" / "*" / ".lake" / "build" / "lib" / "lean")))
    return os.pathsep.join(entries)


def configure(lean_bin: str | None = None, judge_root: str | None = None, lean_path: str | None = None,
              timeout: float = 300.0) -> LeanConfig | None:
    """Resolve a configuration or return None when Lean is not available."""
    lean_bin = lean_bin or os.environ.get("EQTHEORY_LEAN_BIN") or shutil.which("lean")
    lean_path = lean_path or os.environ.get("EQTHEORY_LEAN_PATH")
    judge_root = judge_root or os.environ.get("EQTHEORY_JUDGE_ROOT")
    if lean_path is None and judge_root:
        lean_path = lean_path_for(judge_root)
    if not lean_bin or not lean_path or not Path(lean_bin).exists():
        return None
    return LeanConfig(lean_bin, lean_path, timeout)


def _equation_def(name: str, eq: Equation) -> str:
    binders = " ".join(f"({v} : G)" for v in eq.variables)
    return f"@[reducible] def {name} (G : Type _) [Magma G] : Prop := ∀ {binders}, {eq.text}"


def problem_module(hyp: Equation, goal: Equation, verdict: str) -> str:
    """The judge-controlled ``JudgeProblem`` module for one verdict."""
    target = ("∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G" if verdict == "true"
              else "∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G")
    return ("import JudgeMagma.Magma\n\n"
            f"{_equation_def('EquationLHS', hyp)}\n{_equation_def('EquationRHS', goal)}\n\n"
            f"abbrev Goal : Prop := {target}\n")


def compile_certificate(hyp: Equation, goal: Equation, verdict: str, code: str, cfg: LeanConfig,
          workdir: str | None = None) -> CheckResult:
    """Compile ``JudgeProblem`` for the verdict, then the certificate."""
    t0 = time.monotonic()
    tmp = Path(workdir or tempfile.mkdtemp(prefix="eqtheory-lean-"))
    tmp.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(tmp), cfg.lean_path]))
    src = tmp / "JudgeProblem.lean"
    src.write_text(problem_module(hyp, goal, verdict), encoding="utf-8")
    try:
        p = subprocess.run([cfg.lean_bin, f"--root={tmp}", "-o", str(tmp / "JudgeProblem.olean"), str(src)],
                           cwd=tmp, env=env, text=True, capture_output=True, timeout=cfg.timeout)
        if p.returncode != 0:
            return CheckResult(False, verdict, time.monotonic() - t0, "JudgeProblem: " + (p.stderr or p.stdout))
        sub = tmp / "Submission.lean"
        sub.write_text(code, encoding="utf-8")
        p = subprocess.run([cfg.lean_bin, *LINTER_FLAGS, f"--root={tmp}", str(sub)],
                           cwd=tmp, env=env, text=True, capture_output=True, timeout=cfg.timeout)
    except subprocess.TimeoutExpired:
        return CheckResult(False, verdict, time.monotonic() - t0, "timeout")
    out = (p.stdout or "") + (p.stderr or "")
    ok = p.returncode == 0 and "error" not in out and "sorry" not in out
    return CheckResult(ok, verdict, time.monotonic() - t0, out)


def make_judge(hyp: Equation, goal: Equation, cfg: LeanConfig):
    """A ``judge(verdict, code) -> bool`` closure for :mod:`eqtheory.solve`."""
    return lambda verdict, code: compile_certificate(hyp, goal, verdict, code, cfg).ok
