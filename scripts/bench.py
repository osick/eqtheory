"""Benchmark the library pipeline on a JSONL problem set.

    python scripts/bench.py PROBLEMS.jsonl OUTDIR --shard 0/4 [--llm]
    python scripts/bench.py --report OUTDIR      # summarise all shards

Records: {"id", "equation1", "equation2", "answer": true|false}. Every
certificate is compiled with Lean (EQTHEORY_LEAN_BIN / EQTHEORY_JUDGE_ROOT
must be set); --llm adds the OpenRouter round for problems the
deterministic ladder leaves open (OPENROUTER_API_KEY from the environment).
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from eqtheory import Problem, solve, Config, Trace          # noqa: E402
from eqtheory.lean import check as lean_check               # noqa: E402
from eqtheory.llm import OpenRouterClient                   # noqa: E402


def run(args):
    k, n = (int(x) for x in args.shard.split("/"))
    rows = [json.loads(l) for l in open(args.problems, encoding="utf-8") if l.strip()]
    rows = [r for i, r in enumerate(rows) if i % n == k]
    cfg = lean_check.configure(timeout=args.lean_timeout)
    if cfg is None:
        sys.exit("Lean not configured")
    out = Path(args.outdir) / f"shard-{k}.jsonl"
    done = set()
    if out.exists():
        done = {json.loads(l)["id"] for l in open(out, encoding="utf-8") if l.strip()}
    client = OpenRouterClient() if args.llm else None
    with open(out, "a", encoding="utf-8") as fh:
        for r in rows:
            if r["id"] in done:
                continue
            pr = Problem.parse(r["equation1"], r["equation2"])
            judge = lean_check.make_judge(pr.hypothesis, pr.goal, cfg)
            tr = Trace()
            t0 = time.monotonic()
            calls0 = client.calls if client else 0
            try:
                ans = solve(pr, Config(), judge=judge, complete=client, trace=tr)
                err = None
            except Exception as e:  # noqa: BLE001
                ans, err = None, repr(e)
            rec = {"id": r["id"], "expected": "true" if r["answer"] else "false",
                   "verdict": ans.verdict if ans else None, "stage": ans.stage if ans else None,
                   "verified": ans.verified if ans else None, "seconds": round(time.monotonic() - t0, 1),
                   "llm_calls": (client.calls - calls0) if client else 0,
                   "facts": {"exhausted": tr.facts.exhausted, "searched": tr.facts.searched},
                   "trace": tr.steps, "error": err}
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n"); fh.flush()
            print(f"{r['id']:28s} exp={rec['expected']:5s} got={rec['verdict']} {rec['stage']} {rec['seconds']}s", flush=True)


def report(outdir):
    recs = []
    for f in sorted(Path(outdir).glob("shard-*.jsonl")):
        recs += [json.loads(l) for l in open(f, encoding="utf-8") if l.strip()]
    by_cat = defaultdict(list)
    for r in recs:
        by_cat[r["id"].rsplit("_", 1)[0]].append(r)
    lines = [f"# Library benchmark — {outdir}", "", f"{len(recs)} problems, Lean-checked certificates.", "",
             "| category | n | correct | wrong | no answer | median s | max s |", "|---|---|---|---|---|---|---|"]
    tot = Counter()
    for cat, rs in sorted(by_cat.items()):
        ok = sum(r["verdict"] == r["expected"] for r in rs)
        wrong = sum(r["verdict"] is not None and r["verdict"] != r["expected"] for r in rs)
        none = sum(r["verdict"] is None for r in rs)
        secs = sorted(r["seconds"] for r in rs)
        lines.append(f"| {cat} | {len(rs)} | {ok} | {wrong} | {none} | {secs[len(secs)//2]} | {secs[-1]} |")
        tot.update(ok=ok, wrong=wrong, none=none, n=len(rs))
    lines += ["", f"**Total: {tot['ok']}/{tot['n']} correct, {tot['wrong']} wrong, {tot['none']} unanswered.**", "",
              "## Stages", ""]
    for stage, c in Counter(r["stage"] for r in recs if r["stage"]).most_common():
        lines.append(f"- {stage}: {c}")
    lines += ["", f"LLM calls: {sum(r['llm_calls'] for r in recs)}", "", "## Misses / wrong", ""]
    for r in recs:
        if r["verdict"] != r["expected"]:
            lines.append(f"- {r['id']}: expected {r['expected']}, got {r['verdict']} ({r['stage']}), "
                         f"{r['seconds']}s, facts {r['facts']}, error {r['error']}")
    text = "\n".join(lines) + "\n"
    Path(outdir, "REPORT.md").write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("problems", nargs="?"); p.add_argument("outdir")
    p.add_argument("--shard", default="0/1"); p.add_argument("--llm", action="store_true")
    p.add_argument("--lean-timeout", type=float, default=300.0); p.add_argument("--report", action="store_true")
    a = p.parse_args()
    report(a.outdir) if a.report else run(a)
