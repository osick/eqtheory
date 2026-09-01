"""Settings: one place for every default that is a *choice*, not a theorem.

Resolution order (later wins):

1. the defaults below,
2. a TOML file — ``EQTHEORY_CONFIG`` if set, else ``./eqtheory.toml``,
   else ``~/.config/eqtheory/config.toml`` (keys as in :class:`Settings`,
   optionally under an ``[eqtheory]`` table),
3. environment variables ``EQTHEORY_<FIELD>`` (upper-case field name,
   e.g. ``EQTHEORY_LEAN_TOOLCHAIN``; ``none`` or an empty value clears an
   optional field),
4. programmatic: ``eqtheory.config.configure(lean_toolchain=…)``.

Everything reads ``settings`` at call time, so changes apply immediately.
"""
from __future__ import annotations

import dataclasses
import os
import tomllib
from dataclasses import dataclass, fields
from pathlib import Path
from typing import Any

ENV_PREFIX = "EQTHEORY_"


@dataclass
class Settings:
    # Lean: which toolchain the standalone certificates are pinned to (written to
    # a `lean-toolchain` file next to the certificate so an elan proxy selects it;
    # None = do not pin, use whatever `lean` is found).
    lean_toolchain: str | None = "leanprover/lean4:v4.33.1"
    lean_bin: str | None = None            # explicit binary; else PATH, then elan
    lean_timeout: float = 300.0            # seconds per certificate compile
    lean_max_rec_depth: int = 20_000       # `set_option maxRecDepth` in certificates
    # Models
    model_max_n: int = 12                  # reach of the complete finite search
    sat_memory_mb: float = 1200.0          # budget that picks CDCL vs cell search
    # LLM (OpenAI-compatible chat completions)
    llm_model: str = "openai/gpt-oss-120b"
    llm_base_url: str = "https://openrouter.ai/api/v1"
    llm_api_key_env: str = "OPENROUTER_API_KEY"
    llm_seed: int = 0
    llm_reasoning_effort: str | None = "low"
    llm_provider_order: str | None = None
    llm_max_tokens: int = 6000
    llm_temperature: float = 0.0
    llm_timeout: float = 300.0
    llm_rounds: int = 4

    def as_dict(self) -> dict[str, Any]:
        return dataclasses.asdict(self)


def _coerce(field: dataclasses.Field, value: Any) -> Any:
    t = field.type
    optional = "None" in t
    if value is None or (isinstance(value, str) and value.strip().lower() in ("", "none", "null")):
        return None if optional else field.default
    base = t.replace(" | None", "")
    if base == "int":
        return int(value)
    if base == "float":
        return float(value)
    if base == "bool":
        return str(value).lower() in ("1", "true", "yes", "on")
    return str(value)


def config_file() -> Path | None:
    """The config file that applies, or None."""
    explicit = os.environ.get(ENV_PREFIX + "CONFIG")
    cands = [Path(explicit)] if explicit else [Path("eqtheory.toml"), Path("~/.config/eqtheory/config.toml").expanduser()]
    for c in cands:
        if c.is_file():
            return c
    return None


def load(path: str | os.PathLike | None = None, env: dict | None = None) -> Settings:
    """Build a Settings object from defaults, file and environment."""
    s = Settings()
    known = {f.name: f for f in fields(Settings)}
    file = Path(path) if path else config_file()
    if file is not None:
        data = tomllib.loads(file.read_text(encoding="utf-8"))
        data = data.get("eqtheory", data)
        for k, v in data.items():
            if k in known:
                setattr(s, k, _coerce(known[k], v))
            else:
                raise ValueError(f"{file}: unknown setting {k!r}")
    env = os.environ if env is None else env
    for name, f in known.items():
        raw = env.get(ENV_PREFIX + name.upper())
        if raw is not None:
            setattr(s, name, _coerce(f, raw))
    return s


settings = load()


def configure(**overrides) -> Settings:
    """Set fields programmatically: ``configure(lean_toolchain=None, model_max_n=14)``."""
    known = {f.name: f for f in fields(Settings)}
    for k, v in overrides.items():
        if k not in known:
            raise ValueError(f"unknown setting {k!r}")
        setattr(settings, k, _coerce(known[k], v))
    return settings


def reload(path: str | os.PathLike | None = None) -> Settings:
    """Re-read file and environment into the shared ``settings``."""
    fresh = load(path)
    for f in fields(Settings):
        setattr(settings, f.name, getattr(fresh, f.name))
    return settings


def describe() -> str:
    """Effective settings, one per line, with the config file that applied."""
    lines = [f"config file: {config_file() or '(none)'}"]
    for f in fields(Settings):
        env = ENV_PREFIX + f.name.upper()
        src = "env" if env in os.environ else ("default" if getattr(settings, f.name) == f.default else "file/programmatic")
        lines.append(f"{f.name:22s} = {getattr(settings, f.name)!r:40} [{src}]")
    return "\n".join(lines)


__all__ = ["Settings", "settings", "load", "configure", "reload", "describe", "config_file", "ENV_PREFIX"]
