# CI and releases

## CI

`.github/workflows/ci.yml` runs on every push and pull request:
pyflakes, pytest with coverage (fails under 80 %), a CLI smoke test with
graphviz installed, and a build + `twine check` of sdist and wheel, on
Python 3.11–3.13. A separate `lean` job installs Lean 4 via elan and
compiles every certificate shape (`tests/test_lean.py`).

## Releases

Versions follow SemVer; the tag must equal `v` + `project.version` in
`pyproject.toml` (the release workflow checks this).

```bash
# bump pyproject.toml version and eqtheory/__init__.py __version__, add a CHANGELOG section
git commit -am "release 0.1.0"
git tag -a v0.1.0 -m "eqtheory 0.1.0"
git push origin main --tags
```

`.github/workflows/release.yml` then builds the distributions, creates a
GitHub Release whose notes are the matching CHANGELOG section (with the
sdist/wheel attached), and publishes to PyPI through *trusted
publishing*. One-time setup for PyPI: on pypi.org → your account →
Publishing → add a pending publisher with owner `osick`, repository
`eqtheory`, workflow `release.yml`, environment `pypi`; on GitHub create
the environment `pypi` (Settings → Environments) — optionally with a
required reviewer, which makes every PyPI upload a manual approval.
Until that is configured the `pypi` job fails while the GitHub Release
still succeeds.

Suggested first tags: `v0.1.0` for the state validated in
`artifacts/bench-stress-2026-09-01/REPORT.md`.
