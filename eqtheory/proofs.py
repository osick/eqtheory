"""Proof chains — the certificate-carrying data structure.

Every equality the library derives is accompanied by a *chain*: a list
of links that rewrite a start term into an end term, each link a literal
instance of the hypothesis, of a derived lemma, a reference to a shared
sub-proof, or a congruence step acting on the children of a term.

    ('h',   sigma, forward)          hypothesis instance, sigma = args in
                                     binder order; forward: lhs → rhs
    ('lem', name, sigma, forward)    same for a named derived lemma
    ('ref', name, flipped)           a shared sub-proof (Lean `have`)
    ('cong', left_chain, right_chain) rewrite inside the two children

Chains are *replayed* symbolically before anything is emitted
(:func:`replay`, :func:`validate`): a chain that does not reproduce its
claimed endpoints is discarded. This is the library's soundness gate —
the e-graph and the completion engine may be as clever as they like, the
replay is what is trusted, and Lean re-checks the rendered result.
"""
from __future__ import annotations

from typing import Mapping

from .terms import Term, substitute

Link = tuple
Chain = list

# A rewrite rule as the engines pass it around:
# (kind, name, src, dst, vars, orient) with kind 'h' or 'lem'.
Rule = tuple


def invert(chain: Chain) -> Chain:
    """The chain proving the reverse equality."""
    out: Chain = []
    for link in reversed(chain):
        if link[0] == "h":
            out.append(("h", link[1], not link[2]))
        elif link[0] == "lem":
            out.append(("lem", link[1], link[2], not link[3]))
        elif link[0] == "cong":
            out.append(("cong", invert(link[1]), invert(link[2])))
        else:
            out.append(("ref", link[1], not link[2]))
    return out


def wrap_cong(path: tuple[int, ...], links: Chain) -> Chain:
    """Lift ``links`` (acting at ``path``) to the root via congruence."""
    for d in reversed(path):
        links = [("cong", links, [])] if d == 0 else [("cong", [], links)]
    return links


def rule_link(rule: Rule, ren: Mapping[str, Term], sigma: Mapping[str, Term], forward: bool) -> Link:
    """The link applying ``rule`` in direction ``forward`` under ``sigma``.

    ``ren`` maps the rule's variables to the (renamed) variables used
    during search; ``sigma`` is the substitution found by matching.
    """
    from .terms import resolve
    kind, name, _, _, rvars, orient = rule
    args = tuple(resolve(ren[v], sigma) for v in rvars)
    direction = orient if forward else not orient
    if kind == "h":
        return ("h", args, direction)
    return ("lem", name, args, direction)


def replay(chain: Chain, cur: Term, hyp: tuple, env: Mapping[str, tuple],
           rules: Mapping[str, tuple] | None = None) -> Term:
    """Apply ``chain`` to ``cur`` symbolically; raise ``ValueError`` on any
    link whose source does not match. ``hyp`` = (lhs, rhs, vars) of the
    hypothesis, ``env`` = name → (start, end) of shared sub-proofs,
    ``rules`` = name → (lhs, rhs, vars) of derived lemmas.
    """
    HL, HR, hvars = hyp
    for link in chain:
        if link[0] == "h":
            _, sigma, forward = link
            sub = dict(zip(hvars, sigma))
            src = substitute(HL if forward else HR, sub)
            dst = substitute(HR if forward else HL, sub)
            if cur != src:
                raise ValueError("h-link source mismatch")
            cur = dst
        elif link[0] == "lem":
            _, name, sigma, forward = link
            if not rules or name not in rules:
                raise ValueError(f"unknown rule {name!r}")
            LL, RR, rvars = rules[name]
            sub = dict(zip(rvars, sigma))
            src = substitute(LL if forward else RR, sub)
            dst = substitute(RR if forward else LL, sub)
            if cur != src:
                raise ValueError("lem-link source mismatch")
            cur = dst
        elif link[0] == "cong":
            if isinstance(cur, str):
                raise ValueError("cong link on a variable")
            cur = (replay(link[1], cur[0], hyp, env, rules),
                   replay(link[2], cur[1], hyp, env, rules))
        elif link[0] == "ref":
            _, name, flipped = link
            s, e = env[name]
            src, dst = (e, s) if flipped else (s, e)
            if cur != src:
                raise ValueError("ref-link source mismatch")
            cur = dst
        else:
            raise ValueError(f"unknown link {link[0]!r}")
    return cur


def validate(hyp: tuple, lemmas: list, chain: Chain, start: Term, end: Term,
             rules: Mapping[str, tuple] | None = None) -> bool:
    """Independent replay of a shared proof: every named sub-proof against
    its declared endpoints, then the main chain from ``start`` to ``end``.
    """
    env: dict = {}
    try:
        for name, s, e, sub_chain in lemmas:
            if replay(sub_chain, s, hyp, env, rules) != e:
                return False
            env[name] = (s, e)
        return replay(chain, start, hyp, env, rules) == end
    except (ValueError, KeyError, IndexError, TypeError):
        return False
