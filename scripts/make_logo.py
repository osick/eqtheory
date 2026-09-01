"""Generate docs/logo.svg (and .png) from a real solve.

The motif is the proof the e-graph extracts for
    x = x ◇ y   ⇒   x = (x ◇ y) ◇ z
drawn along the edges of the ◇ symbol: every node is a term of the
proof chain, every edge an instance of the hypothesis `h`.
"""
from __future__ import annotations

import html
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from eqtheory import Problem, prove_goal, render_term          # noqa: E402
from eqtheory.terms import substitute                          # noqa: E402

HYP, GOAL = "x = x ◇ y", "x = (x ◇ y) ◇ z"


def proof_terms():
    p = Problem.parse(HYP, GOAL)
    eg, l, r = prove_goal(p.hypothesis, p.goal, time_budget=5)
    _, chain = eg.explain(l, r)
    cur, terms, labels = p.goal.lhs, [p.goal.lhs], []
    for kind, sigma, forward in chain:                 # this proof is a plain h-chain
        assert kind == "h"
        sub = dict(zip(p.hypothesis.variables, sigma))
        cur = substitute(p.hypothesis.rhs if forward else p.hypothesis.lhs, sub)
        terms.append(cur)
        labels.append("h " + " ".join(render_term(t) for t in sigma))
    assert cur == p.goal.rhs
    return [strip(render_term(t)) for t in terms], labels


def strip(s):
    return s[1:-1] if s.startswith("(") and s.endswith(")") else s


def svg(terms, labels):
    W, H = 860, 230
    cx, cy, R = 150, 115, 85                     # the ◇
    top, left, right, bottom = (cx, cy - R), (cx - R, cy), (cx + R, cy), (cx, cy + R)
    ink, accent, soft, mute = "#1f2937", "#d62828", "#ffd166", "#6b7280"
    font = "DejaVu Sans, Noto Sans, Helvetica, Arial, sans-serif"
    mono = "DejaVu Sans Mono, Menlo, Consolas, monospace"

    def box(x, y, text, fill, anchor="middle"):
        w = 11 * len(text) + 18
        if anchor == "start":
            x += w / 2 - 22
        return (f'<rect x="{x - w / 2:.0f}" y="{y - 14}" width="{w}" height="28" rx="7" fill="{fill}" stroke="{ink}" stroke-width="1.5"/>'
                f'<text x="{x}" y="{y + 5}" text-anchor="middle" font-family="{mono}" font-size="15" fill="{ink}">{html.escape(text)}</text>')

    def edge_label(x, y, text, anchor="middle"):
        return f'<text x="{x}" y="{y}" text-anchor="{anchor}" font-family="{mono}" font-size="12" fill="{accent}">{html.escape(text)}</text>'

    o = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
         f'<rect width="{W}" height="{H}" rx="18" fill="#ffffff"/>',
         '<defs><marker id="a" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">'
         f'<path d="M0,0 L10,5 L0,10 z" fill="{accent}"/></marker></defs>',
         # the diamond
         f'<polygon points="{top[0]},{top[1]} {right[0]},{right[1]} {bottom[0]},{bottom[1]} {left[0]},{left[1]}" '
         f'fill="{soft}" fill-opacity="0.35" stroke="{ink}" stroke-width="3" stroke-linejoin="round"/>',
         # proof edges along the top two sides
         f'<line x1="{left[0] + 26}" y1="{left[1] - 26}" x2="{top[0] - 22}" y2="{top[1] + 22}" stroke="{accent}" stroke-width="3" marker-end="url(#a)"/>',
         f'<line x1="{top[0] + 22}" y1="{top[1] + 22}" x2="{right[0] - 26}" y2="{right[1] - 26}" stroke="{accent}" stroke-width="3" marker-end="url(#a)"/>',
         edge_label(cx - R / 2 - 14, cy - R / 2 - 10, labels[0], "end"),
         edge_label(cx + R / 2 + 14, cy - R / 2 - 10, labels[1], "start"),
         # the terms of the proof
         box(*left, terms[0], "#ffffff"),
         box(top[0], top[1] + 2, terms[1], "#ffffff"),
         box(right[0], right[1], terms[2], "#ffffff", "start"),
         # the verdict
         f'<text x="{cx}" y="{cy + 34}" text-anchor="middle" font-family="{font}" font-size="14" font-weight="700" fill="{ink}">✓ Lean</text>',
         # wordmark
         f'<text x="400" y="112" font-family="{font}" font-size="64" font-weight="700" fill="{ink}">eq<tspan fill="{accent}">theory</tspan></text>',
         f'<text x="402" y="146" font-family="{font}" font-size="17" fill="{mute}">equational theories over magmas</text>',
         f'<text x="402" y="170" font-family="{font}" font-size="14" fill="{mute}">proofs · countermodels · Lean 4 certificates</text>',
         f'<text x="402" y="200" font-family="{mono}" font-size="12" fill="{mute}">{html.escape(HYP)}  ⇒  {html.escape(GOAL)}   — proved above</text>',
         "</svg>"]
    return "\n".join(o)


if __name__ == "__main__":
    terms, labels = proof_terms()
    out = Path(__file__).resolve().parents[1] / "docs" / "logo.svg"
    out.write_text(svg(terms, labels), encoding="utf-8")
    print("wrote", out, terms, labels)
    try:
        subprocess.run(["cairosvg", str(out), "-o", str(out.with_suffix(".png")), "--output-width", "1520"], check=True)
        print("wrote", out.with_suffix(".png"))
    except (OSError, subprocess.CalledProcessError) as err:
        print("png skipped:", err)
