"""Visualisation of e-graphs and proof chains.

``egraph_to_dot`` emits Graphviz DOT: one cluster per e-class, op nodes as
records with edges to their children's classes, variables as ellipses.
``render_egraph`` writes SVG/PNG/PDF via the ``dot`` executable when it is
on PATH and falls back to a dependency-free SVG layout (classes in rows by
creation order) otherwise — so the library has no hard dependency.
"""
from __future__ import annotations

import html
import shutil
import subprocess
from typing import Sequence

from .terms import render_term


def egraph_to_dot(eg, highlight: Sequence[int] = (), proof_pairs: Sequence[tuple[int, int]] = (),
                  max_classes: int | None = None) -> str:
    hl = {eg.find(n) for n in highlight}
    classes = eg.classes()
    order = sorted(classes, key=lambda r: (eg.size[r], r))
    if max_classes is not None:
        order = order[:max_classes]
    keep = set(order)
    out = ["digraph egraph {", "  rankdir=BT;", "  node [fontname=\"monospace\", fontsize=10];",
           "  compound=true;"]
    for rep in order:
        members = classes[rep]
        color = "#ffd166" if rep in hl else "#eeeeee"
        out.append(f"  subgraph cluster_{rep} {{")
        out.append(f"    label=\"c{rep}: {html.escape(render_term(eg.term_of(rep)))}\"; style=filled; fillcolor=\"{color}\";")
        for n in members:
            st = eg.nodes[n]
            if st[0] == "var":
                out.append(f"    n{n} [label=\"{st[1]}\", shape=ellipse];")
            else:
                out.append(f"    n{n} [label=\"◇ #{n}\", shape=box];")
        out.append("  }")
    for rep in order:
        for n in classes[rep]:
            st = eg.nodes[n]
            if st[0] == "op":
                for child in (st[1], st[2]):
                    crep = eg.find(child)
                    if crep in keep:
                        attrs = f"lhead=cluster_{crep}, " if crep != rep else ""
                        out.append(f"  n{n} -> n{crep} [{attrs}color=\"#666666\"];")
    for u, v in proof_pairs:
        out.append(f"  n{u} -> n{v} [color=\"#d62828\", penwidth=2, dir=none, constraint=false];")
    out.append("}")
    return "\n".join(out)


def _svg_fallback(eg, highlight: Sequence[int] = (), max_classes: int | None = None) -> str:
    hl = {eg.find(n) for n in highlight}
    classes = eg.classes()
    order = sorted(classes, key=lambda r: (eg.size[r], r))
    if max_classes is not None:
        order = order[:max_classes]
    w, rowh, colw = 900, 34, 300
    rows = []
    for i, rep in enumerate(order):
        x, y = 10 + (i % 3) * colw, 10 + (i // 3) * rowh
        fill = "#ffd166" if rep in hl else "#eeeeee"
        label = html.escape(f"c{rep} ({len(classes[rep])}): {render_term(eg.term_of(rep))}")[:60]
        rows.append(f'<rect x="{x}" y="{y}" width="{colw - 10}" height="{rowh - 6}" fill="{fill}" stroke="#999"/>'
                    f'<text x="{x + 6}" y="{y + 20}" font-family="monospace" font-size="12">{label}</text>')
    h = 20 + ((len(order) + 2) // 3) * rowh
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}">'
            f'<rect width="100%" height="100%" fill="white"/>' + "".join(rows) + "</svg>")


def render_egraph(eg, path: str, highlight: Sequence[int] = (), proof_pairs: Sequence[tuple[int, int]] = (),
                  max_classes: int | None = 200) -> str:
    """Write the e-graph picture to ``path`` (.svg/.png/.pdf/.dot). Returns
    the renderer used: ``"graphviz"``, ``"svg-fallback"`` or ``"dot"``."""
    fmt = path.rsplit(".", 1)[-1].lower()
    dot = egraph_to_dot(eg, highlight, proof_pairs, max_classes)
    if fmt == "dot":
        open(path, "w", encoding="utf-8").write(dot)
        return "dot"
    exe = shutil.which("dot")
    if exe:
        proc = subprocess.run([exe, f"-T{fmt}", "-o", path], input=dot.encode("utf-8"), capture_output=True)
        if proc.returncode == 0:
            return "graphviz"
    if fmt != "svg":
        raise RuntimeError("graphviz `dot` not available; only .svg/.dot can be written without it")
    open(path, "w", encoding="utf-8").write(_svg_fallback(eg, highlight, max_classes))
    return "svg-fallback"


def chain_to_dot(lemmas: list, chain: list, title: str = "proof") -> str:
    """The `have` dependency graph of a shared proof."""
    out = ["digraph proof {", "  node [fontname=\"monospace\", fontsize=10, shape=box];"]
    for name, s, e, sub in lemmas:
        out.append(f"  {name} [label=\"{name}: {html.escape(render_term(s))} = {html.escape(render_term(e))}\"];")
    out.append(f"  main [label=\"{html.escape(title)}\", style=filled, fillcolor=\"#ffd166\"];")

    def refs(ch, acc):
        for link in ch:
            if link[0] == "ref":
                acc.add(link[1])
            elif link[0] == "cong":
                refs(link[1], acc); refs(link[2], acc)
        return acc
    for name, _, _, sub in lemmas:
        for dep in sorted(refs(sub, set())):
            out.append(f"  {dep} -> {name};")
    for dep in sorted(refs(chain, set())):
        out.append(f"  {dep} -> main;")
    out.append("}")
    return "\n".join(out)
