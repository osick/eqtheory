"""An LLM stage as a library component.

The deterministic engines decide the vast majority of implications; the
LLM stage is for the residue. What made it *safe* in the Stage-2 solver
is not the model but the hygiene around it, all of which is here:

* a **configurable prompt** (:data:`DEFAULT_PROMPT`, or your own string /
  file with the same placeholders) that carries the search facts —
  which sizes are *proven* free of countermodels — and the negative
  knowledge of what the deterministic prover already tried;
* **preflight** rejection of proof holes, non-existent library lemmas
  and unavailable automation before a Lean round is paid for;
* **dedupe** of repeated proposals and a verdict-flip nudge;
* False proposals are **verified numerically** here (a table or affine
  parameters are checked against both equations), True proposals need a
  Lean ``judge`` callback — without one they are returned *unverified*.

The transport is pluggable: any ``Completer`` — a callable
``prompt -> str`` — works; :class:`OpenRouterClient` covers the
OpenAI-compatible chat API with stdlib HTTP only.
"""
from __future__ import annotations

import json
import os
import re
import time
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from typing import Callable, Sequence

from .config import settings
from .lean import certs
from .models.finite import is_countermodel
from .terms import Equation, Problem

Completer = Callable[[str], str]

DEFAULT_PROMPT = """You are deriving an equational implication over magmas in Lean 4.
A magma has one binary operator written `◇` (U+25C7 white diamond,
left-associative) on variables a-z, with parens for grouping.

CRITICAL operator note: the Lean `Magma` class binds the operator to `◇`,
not `*`. Write every operator as `◇` in your proof body.

Hypothesis:  {hypothesis}
Goal:        {goal}

CRITICAL: a general magma obeys NO algebraic laws beyond the hypothesis. Do NOT
assume associativity, commutativity, idempotence, cancellation, identity,
inverses, or distributivity unless the hypothesis itself states it.

You will return a Lean 4 tactic body that closes this goal:

    def submission : Goal := by
      intro G _ h
      <YOUR TACTICS HERE>

`h` is the ONLY hypothesis available, quantified over G. Instantiate it with
`h x y z ...`; `.symm` flips it; `.trans` chains. `intro G _ h` has ALREADY
been executed — never repeat it. If the goal is universally quantified, your
FIRST tactic must introduce exactly the goal's variables, e.g. `intro x y`.

Useful patterns:
- Instantiate:           have e1 := h a b c
- Chain transitively:    exact (h a b c).trans (h b c a).symm
- Calc chain:            calc lhs = mid := h ...
                              _ = rhs := (h ...).symm
- Independence trick: if a variable appears on only ONE side of the hypothesis,
  the other side is independent of it: `(h u1 ...).symm.trans (h u2 ...)`.
- Rewrite INSIDE a compound term: `congrArg (t ◇ ·) p` lifts `p : a = b` to
  `t ◇ a = t ◇ b`; `congrArg (· ◇ t) p` lifts it to `a ◇ t = b ◇ t`.
- Last-resort finisher: after one or two `have k := h a a a`, `grind`.

THE MATCH-COLLAPSE METHOD: substitute COMPOUND terms into h's variables so
the resulting equation's outer structure equals the goal's, then equate the
leftover inner terms through variables free on one side of h and lift with
`congrArg`.

Style rules: the name is `congrArg` (not `congr_arg`); never reference names
you did not introduce; each calc step's left side repeats the previous right
side. Forbidden: proof holes, `Equation<N>_implies_Equation<M>` lemmas, bare
`simp`, Mathlib-only tactics (`ring`, `linarith`, `aesop`, ...).

If you become convinced the implication is FALSE, answer with a
counterexample: a multiplication table on Fin n (2 <= n <= 12, row-major)
that satisfies the hypothesis but breaks the goal, or for larger n an AFFINE
magma a ◇ b = (p·a + q·b + r) mod n as {{"n": n, "p": p, "q": q, "r": r}}.
Hand-verify the hypothesis on it before answering.

What the deterministic machine search has established for THIS problem:
{search_facts}

What the deterministic PROVER already tried (every item FAILED):
{tried}

Round: {round}
Previous attempts in this conversation:
{previous_attempts}

Respond with EXACTLY ONE JSON object, no markdown fences, in one shape:
  {{"verdict": "true",  "proof": "<tactic body, no `by`, no imports>"}}
  {{"verdict": "false", "counterexample_table": [[0,1],[1,0]]}}
  {{"verdict": "false", "affine": {{"n": 12, "p": 1, "q": 2, "r": 0}}}}
"""

PLACEHOLDERS = ("hypothesis", "goal", "search_facts", "tried", "round", "previous_attempts")


def load_prompt(path: str) -> str:
    """Read a prompt template file; it must use the :data:`PLACEHOLDERS`."""
    text = open(path, encoding="utf-8").read()
    missing = [p for p in ("hypothesis", "goal") if "{" + p + "}" not in text]
    if missing:
        raise ValueError(f"prompt template lacks placeholders: {missing}")
    return text


def render_prompt(template: str, problem: Problem, *, search_facts: str = "", tried: str = "",
                  round_no: int = 0, previous_attempts: Sequence[str] = ()) -> str:
    return template.format(hypothesis=problem.hypothesis.text, goal=problem.goal.text,
                           search_facts=search_facts or "- nothing yet.", tried=tried or "(nothing recorded)",
                           round=round_no, previous_attempts="\n".join(previous_attempts) or "(none yet)")


def format_search_facts(exhausted: Sequence[int] = (), searched: Sequence[int] = ()) -> str:
    """Two tiers kept apart: sizes *proven* empty vs sizes only swept."""
    proven = sorted(set(exhausted))
    swept = sorted(set(searched) - set(proven))
    lines = []
    if proven:
        lines.append("- " + ", ".join(f"Fin {n}" for n in proven) + ": EVERY magma of that size was enumerated "
                     "and none refutes the goal. That is a proof, not a failed search: IF the implication is "
                     "false, its counterexample is strictly LARGER — never answer with a table of one of them.")
    if swept:
        lines.append("- " + ", ".join(f"Fin {n}" for n in swept) + ": large structured, affine, bilinear and "
                     "pseudo-random families were searched without a hit.")
    return "\n".join(lines) if lines else "- nothing yet: no size has been ruled out."


# ── response handling ────────────────────────────────────────────────────

def extract_json(text: str):
    """The last verdict-bearing JSON object in a response (think tags and
    fences stripped; balanced decode at every brace)."""
    text = re.sub(r"<think>[\s\S]*?</think>", "", text).strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text).strip()
    try:
        return json.loads(text)
    except Exception:
        pass
    dec = json.JSONDecoder()
    best = fallback = None
    for m in re.finditer(r"\{", text):
        try:
            obj, _ = dec.raw_decode(text, m.start())
        except ValueError:
            continue
        if isinstance(obj, dict):
            if "verdict" in obj:
                best = obj
            elif fallback is None:
                fallback = obj
    return best if best is not None else fallback


_TEMPLATE_PRELUDE = re.compile(r"^\s*intro\s+G\s+_\s+h\s*\n?", re.MULTILINE)
_INTRO_LINE = re.compile(r"^(\s*)intro\b.*$")
BANNED_AUTOMATION = ("ring", "linarith", "nlinarith", "aesop", "norm_num", "positivity", "polyrith", "field_simp",
                     "tauto", "omega_nat", "simp_all", "simp?", "exact?", "apply?", "rw?", "decide!")


def clean_proof_body(body: str) -> str:
    """Undo the model habits that kill compiles: `*` for `◇`, a repeated
    template prelude, imports, and an indented block after `intro`."""
    if ":= by" in body:
        body = re.sub(r"^.*?:=\s*by\s*\n?", "", body, count=1, flags=re.DOTALL)
    body = re.sub(r"^\s*by\s+", "", body)
    body = re.sub(r"^\s*import\s+.*\n?", "", body, flags=re.MULTILINE).strip()
    body = body.replace("*", "◇")
    body = _TEMPLATE_PRELUDE.sub("", body, count=1)
    lines, out, i = body.split("\n"), [], 0
    while i < len(lines):
        out.append(lines[i])
        m = _INTRO_LINE.match(lines[i])
        if m is None:
            i += 1
            continue
        base, j, block = len(m.group(1)), i + 1, []
        while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > base):
            block.append(lines[j]); j += 1
        text = [ln for ln in block if ln.strip()]
        if not text:
            i += 1
            continue
        shift = min(len(ln) - len(ln.lstrip()) for ln in text) - base
        out.extend(ln[shift:] if ln.strip() else ln for ln in block)
        i = j
    return "\n".join(out)


def preflight(body: str) -> str | None:
    """Reason to reject without a Lean round, or None."""
    for hole in ("sorry", "admit"):
        if re.search(r"\b" + hole + r"\b", body):
            return f"Proof contains `{hole}`. Provide a complete proof."
    if re.search(r"∀\s*\([^)]*\)\s*,\s*_\s*:=", body):
        return "`have` uses `_` as the type — write the explicit statement."
    lib = re.search(r"Equation\d+_implies_Equation\d+", body)
    if lib:
        return f"`{lib.group()}` does not exist — derive the proof from `h` directly."
    if re.search(r"^\s*simp\b(?!\s+only\b)", body, re.MULTILINE):
        return "Bare `simp` is banned; use `simp only [h]` or an explicit chain."
    for tac in BANNED_AUTOMATION:
        if re.search(rf"^\s*{re.escape(tac)}\b", body, re.MULTILINE):
            return f"`{tac}` is not available; use intro/exact/have/calc/rw/congrArg or grind."
    return None


# ── transport ────────────────────────────────────────────────────────────

@dataclass
class OpenRouterClient:
    """OpenAI-compatible chat completions with stdlib HTTP. Defaults come
    from :mod:`eqtheory.config`; the API key is read from the environment
    variable named by ``api_key_env`` (or passed) and never logged."""
    model: str = field(default_factory=lambda: settings.llm_model)
    seed: int = field(default_factory=lambda: settings.llm_seed)
    reasoning_effort: str | None = field(default_factory=lambda: settings.llm_reasoning_effort)
    provider_order: str | None = field(default_factory=lambda: settings.llm_provider_order)
    base_url: str = field(default_factory=lambda: settings.llm_base_url)
    timeout: float = field(default_factory=lambda: settings.llm_timeout)
    max_tokens: int = field(default_factory=lambda: settings.llm_max_tokens)
    temperature: float = field(default_factory=lambda: settings.llm_temperature)
    api_key: str | None = None
    api_key_env: str = field(default_factory=lambda: settings.llm_api_key_env)
    attempts: int = 3
    calls: int = field(default=0, init=False)
    tokens: dict = field(default_factory=lambda: {"input": 0, "output": 0}, init=False)

    def __call__(self, prompt: str) -> str:
        key = self.api_key or os.environ.get(self.api_key_env)
        if not key:
            raise RuntimeError(f"{self.api_key_env} not set")
        payload = {"model": self.model, "messages": [{"role": "user", "content": prompt}],
                   "max_tokens": self.max_tokens, "temperature": self.temperature, "seed": self.seed}
        if self.reasoning_effort:
            payload["reasoning"] = {"effort": self.reasoning_effort}
        if self.provider_order:
            payload["provider"] = {"order": [self.provider_order]}
        last = None
        for k in range(self.attempts):
            req = urllib.request.Request(f"{self.base_url.rstrip('/')}/chat/completions",
                                         data=json.dumps(payload).encode("utf-8"), method="POST",
                                         headers={"Authorization": f"Bearer {key}", "Content-Type": "application/json"})
            try:
                with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                break
            except (TimeoutError, OSError, urllib.error.URLError, json.JSONDecodeError) as err:
                last = err
                if k < self.attempts - 1:
                    time.sleep((2.0, 8.0)[min(k, 1)])
        else:
            raise RuntimeError(f"request failed after {self.attempts} attempts: {last}")
        self.calls += 1
        usage = data.get("usage") or {}
        self.tokens["input"] += usage.get("prompt_tokens", 0) or 0
        self.tokens["output"] += usage.get("completion_tokens", 0) or 0
        msg = ((data.get("choices") or [{}])[0]).get("message") or {}
        return msg.get("content") or msg.get("reasoning") or ""


# ── the stage ────────────────────────────────────────────────────────────

@dataclass
class LLMOutcome:
    verdict: str | None
    code: str | None
    verified: bool
    rounds: int
    attempts: list = field(default_factory=list)


def llm_stage(problem: Problem, complete: Completer, *, judge: Callable[[str, str], bool] | None = None,
              max_rounds: int = 4, prompt: str = DEFAULT_PROMPT, search_facts: str = "", tried: str = "",
              deadline: float | None = None) -> LLMOutcome:
    """Ask, clean, preflight, verify, feed the error back — for up to
    ``max_rounds`` rounds. False proposals are verified numerically; True
    proposals through ``judge`` when given, otherwise returned unverified."""
    hyp, goal = problem.hypothesis, problem.goal
    prev: list[str] = []
    seen: dict = {}
    failed_true = 0
    for rnd in range(max_rounds):
        if deadline is not None and time.monotonic() >= deadline:
            break
        text = complete(render_prompt(prompt, problem, search_facts=search_facts, tried=tried, round_no=rnd,
                                      previous_attempts=prev))
        ans = extract_json(text)
        if not isinstance(ans, dict) or ans.get("verdict") not in ("true", "false"):
            prev.append(f"Attempt {rnd + 1}: not a valid JSON object with a verdict. Return exactly one JSON object.")
            continue
        if ans["verdict"] == "true":
            body = clean_proof_body(str(ans.get("proof") or ""))
            if not body:
                prev.append(f"Attempt {rnd + 1}: verdict=true but `proof` empty.")
                continue
            err = preflight(body)
            if err:
                prev.append(f"Attempt {rnd + 1}: preflight rejected the proof: {err}")
                continue
            key = re.sub(r"\s+", " ", body)
            if key in seen:
                failed_true += 1
                prev.append(f"Attempt {rnd + 1}: IDENTICAL to attempt {seen[key]} — change the structure or switch verdict."
                            + (" Several proofs failed: seriously consider FALSE." if failed_true >= 2 else ""))
                continue
            seen[key] = rnd + 1
            code = certs.true_code(body, hyp, goal)
            if judge is None:
                return LLMOutcome("true", code, False, rnd + 1, prev)
            if judge("true", code):
                return LLMOutcome("true", code, True, rnd + 1, prev)
            failed_true += 1
            prev.append(f"Attempt {rnd + 1}: Lean rejected the proof `{key[:160]}`."
                        + (" Several proofs failed: seriously consider FALSE." if failed_true >= 2 else ""))
        else:
            tbl, aff = ans.get("counterexample_table"), ans.get("affine")
            if not tbl and isinstance(aff, dict):
                try:
                    n, p, q, r = (int(aff.get(k, 0)) for k in ("n", "p", "q", "r"))
                except (TypeError, ValueError):
                    n = 0
                if not 2 <= n <= 60:
                    prev.append(f"Attempt {rnd + 1}: `affine` needs integer n in 2..60 and p, q, r.")
                    continue
                tbl = [[(p * i + q * j + r) % n for j in range(n)] for i in range(n)]
            if not isinstance(tbl, list) or not tbl:
                prev.append(f"Attempt {rnd + 1}: verdict=false but no table / affine parameters.")
                continue
            key = "F:" + json.dumps(tbl)
            if key in seen:
                prev.append(f"Attempt {rnd + 1}: IDENTICAL countermodel to attempt {seen[key]}.")
                continue
            seen[key] = rnd + 1
            n = len(tbl)
            ok = (all(isinstance(row, list) and len(row) == n for row in tbl)
                  and all(isinstance(v, int) and 0 <= v < n for row in tbl for v in row) and 2 <= n)
            if not ok:
                prev.append(f"Attempt {rnd + 1}: table is not a square n×n table with entries 0..n-1.")
                continue
            if not is_countermodel(hyp, goal, n, tbl):
                bad = "the hypothesis fails" if not hyp_holds(hyp, tbl) else "the goal does NOT fail"
                prev.append(f"Attempt {rnd + 1}: on your table {bad} — it is not a countermodel.")
                continue
            return LLMOutcome("false", certs.false_code(n, tbl, hyp, goal), True, rnd + 1, prev)
    return LLMOutcome(None, None, False, len(prev), prev)


def hyp_holds(hyp: Equation, table) -> bool:
    from .terms import holds
    return holds(hyp, lambda a, b: table[a][b], len(table))
