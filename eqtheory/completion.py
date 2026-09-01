"""Ordered completion and goal-directed superposition with proof chains.

The engine derives *universal lemmas* from a hypothesis by overlapping
oriented rules (Knuth–Bendix critical pairs): where a subterm of one
rule's left side unifies with another rule's left side, the overlapped
term rewrites two ways, and the pair of results is a new equation whose
proof is "undo the first rule, apply the second at the overlap position".
Every candidate carries such a chain and is *replayed* before acceptance;
an unsound candidate is dropped.

Three ingredients make this practical (all measured on the 2026 Stage-2
residue, see the repository reports):

* **Budgets in candidate equations, not seconds** — deterministic and
  independent of machine load.
* **Goal direction** — a ``stop`` predicate ends the completion the moment
  an accepted lemma has the goal as a substitution instance
  (:func:`goal_instance`, one-way matching with rigid goal variables).
* **Interreduction under the ground KBO** — candidates are normalised
  against the lemmas derived so far, with the chain extended so it still
  proves what it is attached to; the KBO gate (:func:`rewrite_step`)
  guarantees termination and lets weight-preserving equations rewrite in
  one consistent direction.
"""
from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Callable, Iterator, Sequence

from .proofs import Chain, invert, rule_link, validate, wrap_cong
from .terms import (Equation, Term, kbo_greater, match, positions, rename, replace_at,
                    resolve, term_leaves, term_vars, unify)

BINDERS = "abcdefghijklmnopqrstuvwxyz"
INTERREDUCE_MAX_STEPS = 40      # belt and braces; KBO already terminates

Lemma = dict   # {name, vars, lhs, rhs, chain}
Rule = tuple   # (kind, name, src, dst, vars, orient)


# ── rewriting ────────────────────────────────────────────────────────────

def rewrite_step(term: Term, rules: Sequence[Rule]):
    """One ordered rewrite of ``term`` (outermost-first): the rule's
    variables bind, the term's do not, and the result must be strictly
    smaller in the ground KBO. Returns (new_term, path, rule, sub) or None."""
    for path, sub_t in positions(term):
        for rule in rules:
            _, _, src, dst, rvars, _ = rule
            sub = match(src, sub_t)
            if sub is None:
                continue
            if any(v not in sub for v in term_vars(dst)):
                continue
            new_t = replace_at(term, path, resolve(dst, sub))
            if kbo_greater(term, new_t):
                return new_t, path, rule, sub
    return None


def interreduce(lhs: Term, rhs: Term, chain: Chain, rules: Sequence[Rule]):
    """Normalise both sides against ``rules``, extending ``chain`` so it
    still proves ``lhs = rhs``. Returns (lhs, rhs, chain)."""
    for _ in range(INTERREDUCE_MAX_STEPS):
        step = rewrite_step(lhs, rules)
        if step is None:
            break
        lhs, path, rule, sub = step
        link = rule_link(rule, {v: v for v in rule[4]}, sub, True)
        chain = invert(wrap_cong(path, [link])) + chain
    for _ in range(INTERREDUCE_MAX_STEPS):
        step = rewrite_step(rhs, rules)
        if step is None:
            break
        rhs, path, rule, sub = step
        link = rule_link(rule, {v: v for v in rule[4]}, sub, True)
        chain = chain + wrap_cong(path, [link])
    return lhs, rhs, chain


def rewrite_rules(hyp: Equation, lemmas: Sequence[Lemma]) -> list[Rule]:
    """Every oriented rule: the hypothesis collapse rule (rhs → lhs) and
    both directions of every derived lemma."""
    rules = [("h", None, hyp.rhs, hyp.lhs, tuple(hyp.variables), False)]
    for lem in lemmas:
        vs = tuple(lem["vars"])
        rules.append(("lem", lem["name"], lem["lhs"], lem["rhs"], vs, True))
        rules.append(("lem", lem["name"], lem["rhs"], lem["lhs"], vs, False))
    return rules


# ── chains over lemma variables ──────────────────────────────────────────

def chain_vars(chain: Chain, acc: list | None = None) -> list[str]:
    if acc is None:
        acc = []
    for link in chain:
        if link[0] == "h":
            for t in link[1]:
                term_vars(t, acc)
        elif link[0] == "lem":
            for t in link[2]:
                term_vars(t, acc)
        elif link[0] == "cong":
            chain_vars(link[1], acc)
            chain_vars(link[2], acc)
    return acc


def rename_chain(links: Chain, mapping) -> Chain:
    out: Chain = []
    for link in links:
        if link[0] == "h":
            out.append(("h", tuple(rename(t, mapping) for t in link[1]), link[2]))
        elif link[0] == "lem":
            out.append(("lem", link[1], tuple(rename(t, mapping) for t in link[2]), link[3]))
        elif link[0] == "ref":
            out.append(link)
        else:
            out.append(("cong", rename_chain(link[1], mapping), rename_chain(link[2], mapping)))
    return out


def canon_lemma(lhs: Term, rhs: Term, chain: Chain):
    """Rename variables to a, b, c, … in first-appearance order (lhs, rhs,
    then chain arguments) for stable dedup keys and Lean binders."""
    mapping: dict = {}

    def note(t):
        if isinstance(t, str):
            if t not in mapping:
                mapping[t] = BINDERS[len(mapping)]
        else:
            note(t[0]); note(t[1])

    def note_chain(links):
        for link in links:
            if link[0] == "h":
                for t in link[1]:
                    note(t)
            elif link[0] == "lem":
                for t in link[2]:
                    note(t)
            elif link[0] == "cong":
                note_chain(link[1]); note_chain(link[2])

    note(lhs); note(rhs); note_chain(chain)
    return rename(lhs, mapping), rename(rhs, mapping), rename_chain(chain, mapping)


# ── critical pairs ───────────────────────────────────────────────────────

def overlap_pairs(hyp: Equation, lemmas: Sequence[Lemma], since: int = 0) -> Iterator[tuple[Rule, Rule]]:
    """Rule pairs worth overlapping in a completion round: at least one
    derived lemma, and at least one rule newer than ``since`` lemmas
    (frontier rounds — pairs of two old rules were done already)."""
    rules = rewrite_rules(hyp, lemmas)
    first_new = 1 + 2 * since
    for i, a in enumerate(rules):
        for j, b in enumerate(rules):
            if a[0] == "h" and b[0] == "h":
                continue
            if i < first_new and j < first_new:
                continue
            yield a, b


def push_overlap(rule_a: Rule, rule_b: Rule, push: Callable) -> None:
    """Critical pairs of two oriented rules with their chains: where
    ``sA|p`` unifies with ``sB``, σ(sA) rewrites to σ(tA) by A and to
    σ(sA[p ← tB]) by B."""
    _, _, sA, tA, varsA, _ = rule_a
    _, _, sB, tB, varsB, _ = rule_b
    renA = {v: v + "1" for v in varsA}
    renB = {v: v + "2" for v in varsB}
    sA_r, tA_r = rename(sA, renA), rename(tA, renA)
    sB_r, tB_r = rename(sB, renB), rename(tB, renB)
    for path, sub in positions(sA_r):
        if isinstance(sub, str):
            continue
        sigma = unify(sub, sB_r)
        if sigma is None:
            continue
        a = resolve(tA_r, sigma)
        b = resolve(replace_at(sA_r, path, tB_r), sigma)
        chain = [rule_link(rule_a, renA, sigma, False)] + wrap_cong(path, [rule_link(rule_b, renB, sigma, True)])
        push(a, b, chain)


# ── the derivation loop ──────────────────────────────────────────────────

@dataclass
class Budget:
    """Search limits. ``nodes`` counts candidate equations (deterministic);
    ``deadline`` (monotonic seconds) is only a backstop."""
    max_lemmas: int = 16
    size_cap: int = 9
    rounds: int = 1
    nodes: int | None = None
    deadline: float | None = None
    interreduce: bool = False


def derive_lemmas(hyp: Equation, budget: Budget = Budget(), *, stop: Callable[[Lemma], bool] | None = None,
                  on_candidate: Callable | None = None) -> list[Lemma]:
    """Universal lemmas derived from ``hyp`` by ordered completion.

    Generators: (1) constancy lemmas from one-sided variables, (2) critical
    pairs of the hypothesis with a renamed copy of itself, (3) further
    rounds overlapping derived lemmas with the hypothesis and each other.
    Every candidate's chain is replayed before acceptance. ``stop`` makes
    the search goal-directed; ``on_candidate`` observes every candidate.
    """
    HL, HR, hvars = hyp.lhs, hyp.rhs, list(hyp.variables)
    hyp_t = (HL, HR, hvars)
    out: list[Lemma] = []
    seen: set = set()
    spent = [0]
    halted = [False]

    def push(lhs, rhs, chain):
        if halted[0]:
            return
        if budget.nodes is not None and spent[0] >= budget.nodes:
            halted[0] = True
            return
        if budget.deadline is not None and time.monotonic() >= budget.deadline:
            halted[0] = True
            return
        spent[0] += 1
        if on_candidate is not None:
            on_candidate((lhs, rhs))
        if lhs == rhs or len(out) >= budget.max_lemmas:
            return
        if budget.interreduce and out:
            lhs, rhs, chain = interreduce(lhs, rhs, chain, rewrite_rules(hyp, out)[1:])
            if lhs == rhs:
                return
        if term_leaves(lhs) > budget.size_cap or term_leaves(rhs) > budget.size_cap:
            return
        lhs, rhs, chain = canon_lemma(lhs, rhs, chain)
        stmt = term_vars(lhs)
        term_vars(rhs, stmt)
        free = [v for v in chain_vars(chain) if v not in stmt]
        if free:
            if not stmt:
                return
            chain = rename_chain(chain, {v: stmt[0] for v in free})
        key = (repr(lhs), repr(rhs))
        if key in seen or (repr(rhs), repr(lhs)) in seen:
            return
        rules = {lm["name"]: (lm["lhs"], lm["rhs"], tuple(lm["vars"])) for lm in out}
        if not validate(hyp_t, [], chain, lhs, rhs, rules):
            return
        seen.add(key)
        vs = term_vars(lhs)
        term_vars(rhs, vs)
        out.append({"name": f"lem{len(out) + 1}", "vars": tuple(vs), "lhs": lhs, "rhs": rhs, "chain": chain})
        if stop is not None and stop(out[-1]):
            halted[0] = True

    lv, rv = set(term_vars(HL)), set(term_vars(HR))
    for f in sorted(rv - lv):
        sa = {v: (f + "A" if v == f else v) for v in hvars}
        sb = {v: (f + "B" if v == f else v) for v in hvars}
        push(rename(HR, sa), rename(HR, sb),
             [("h", tuple(sa[v] for v in hvars), False), ("h", tuple(sb[v] for v in hvars), True)])
    for f in sorted(lv - rv):
        sa = {v: (f + "A" if v == f else v) for v in hvars}
        sb = {v: (f + "B" if v == f else v) for v in hvars}
        push(rename(HL, sa), rename(HL, sb),
             [("h", tuple(sa[v] for v in hvars), True), ("h", tuple(sb[v] for v in hvars), False)])

    ren1 = {v: v + "1" for v in hvars}
    ren2 = {v: v + "2" for v in hvars}
    L1, R1 = rename(HL, ren1), rename(HR, ren1)
    L2, R2 = rename(HL, ren2), rename(HR, ren2)
    for path, sub_t in positions(R1):
        if halted[0]:
            break
        if isinstance(sub_t, str):
            continue
        sig = unify(sub_t, R2)
        if sig is None:
            continue
        a = resolve(L1, sig)
        b = resolve(replace_at(R1, path, L2), sig)
        sig1 = tuple(resolve(ren1[v], sig) for v in hvars)
        sig2 = tuple(resolve(ren2[v], sig) for v in hvars)
        push(a, b, [("h", sig1, True)] + wrap_cong(path, [("h", sig2, False)]))

    since = 0
    for _ in range(max(0, budget.rounds - 1)):
        if halted[0] or len(out) >= budget.max_lemmas:
            break
        before = len(out)
        for ra, rb in overlap_pairs(hyp, list(out), since):
            if halted[0] or len(out) >= budget.max_lemmas:
                break
            push_overlap(ra, rb, push)
        if len(out) == before:
            break
        since = before
    return out


# ── goal-directed superposition ──────────────────────────────────────────

def goal_instance(lem: Lemma, goal_lhs: Term, goal_rhs: Term):
    """Is the goal a substitution instance of ``lem`` (either orientation)?
    Returns (args in binder order, flipped) or None."""
    for lhs, rhs, flipped in ((lem["lhs"], lem["rhs"], False), (lem["rhs"], lem["lhs"], True)):
        sub = match(lhs, goal_lhs)
        if sub is None:
            continue
        sub = match(rhs, goal_rhs, sub)
        if sub is None:
            continue
        filler = goal_lhs if isinstance(goal_lhs, str) else goal_rhs
        return tuple(sub.get(v, filler) for v in lem["vars"]), flipped
    return None


# (size_cap, rounds, node_budget, max_lemmas, interreduce) — the ladder
# measured in the Stage-2 solver; escalates reach before volume.
DEFAULT_LADDER = ((9, 4, 2_000, 2_000, False),
                  (13, 8, 8_000, 8_000, True),
                  (13, 8, 30_000, 30_000, False),
                  (16, 10, 150_000, 150_000, False),
                  (16, 14, 400_000, 400_000, False))
DEEP_LADDER = ((13, 10, 60_000, 60_000, True),)


@dataclass
class SuperpositionProof:
    lemma: Lemma
    args: tuple
    flipped: bool
    derived: list = field(repr=False)


def prove_by_superposition(hyp: Equation, goal: Equation, ladder=DEFAULT_LADDER,
                           deadline: float | None = None) -> SuperpositionProof | None:
    """Run the ladder; stop the moment an accepted lemma has the goal as an
    instance. Returns the lemma, its instantiation and the derived set
    it depends on — everything the certificate needs — or None."""
    for size_cap, rounds, nodes, max_lemmas, inter in ladder:
        if deadline is not None and time.monotonic() >= deadline:
            return None
        hit: dict = {}

        def stop(lem, _hit=hit):
            found = goal_instance(lem, goal.lhs, goal.rhs)
            if found is None:
                return False
            _hit["lem"], _hit["args"], _hit["flipped"] = lem, found[0], found[1]
            return True

        try:
            derived = derive_lemmas(hyp, Budget(max_lemmas, size_cap, rounds, nodes, deadline, inter), stop=stop)
        except (ValueError, RecursionError, MemoryError):
            return None
        if "lem" in hit:
            return SuperpositionProof(hit["lem"], hit["args"], hit["flipped"], derived)
    return None


SEED_SETTINGS = (("wide", Budget(120, 13, 8, 8_000, None, True)),
                 ("plain", Budget(16, 9, 1)))
SEED_SIZES = (4, 12, 32)


def seed_lemmas(hyp: Equation, settings=SEED_SETTINGS, sizes=SEED_SIZES,
                deadline: float | None = None) -> Iterator[tuple[str, list[Lemma], list[Lemma]]]:
    """Smallest-first lemma seeds for an external rewriter (Lean's
    ``grind``): yields (label, seed_lemmas, whole_derived_set). Measured:
    the four smallest lemmas nearly always suffice; a bigger seed is worse."""
    for tag, b in settings:
        if deadline is not None and time.monotonic() >= deadline:
            return
        b = Budget(b.max_lemmas, b.size_cap, b.rounds, b.nodes, deadline, b.interreduce)
        derived = derive_lemmas(hyp, b)
        if not derived:
            continue
        ranked = sorted(derived, key=lambda lem: (term_leaves(lem["lhs"]) + term_leaves(lem["rhs"]), lem["name"]))
        for want in sizes:
            k = min(want, len(ranked))
            if k == 0:
                continue
            yield f"{tag},{k}", ranked[:k], derived
            if k == len(ranked):
                break
