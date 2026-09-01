"""Reference composition: a complete solver for equational implications
in ~60 lines on top of eqtheory.

    python examples/single_file_solver.py "x = y ◇ (x ◇ y)" "x = (x ◇ y) ◇ x"
    python examples/single_file_solver.py --lean ...     # certificates checked

Finds Lean via PATH/elan (or EQTHEORY_LEAN_BIN) for the optional check
and OPENROUTER_API_KEY for the optional LLM round (--llm).
"""
import sys
import time

from eqtheory import Problem, solve, Config, Trace
from eqtheory.lean import check as lean_check
from eqtheory.llm import OpenRouterClient


def main(argv):
    flags = [a for a in argv if a.startswith("--")]
    args = [a for a in argv if not a.startswith("--")]
    if len(args) != 2:
        sys.exit(__doc__)
    problem = Problem.parse(*args)
    judge = None
    if "--lean" in flags:
        cfg = lean_check.configure()
        if cfg is None:
            sys.exit("no Lean 4 binary found (install via elan or set EQTHEORY_LEAN_BIN)")
        judge = lean_check.make_judge(cfg, problem.hypothesis, problem.goal)
    complete = OpenRouterClient() if "--llm" in flags else None
    trace = Trace()
    t0 = time.monotonic()
    answer = solve(problem, Config(model_budget=60, superposition_budget=300), judge=judge,
                   complete=complete, trace=trace)
    for stage, seconds, note in trace.steps:
        print(f"{stage:24s} {seconds:8.2f}s  {note}")
    if answer is None:
        print(f"no answer after {time.monotonic() - t0:.1f}s; sizes proven empty: {trace.facts.exhausted}")
        return 1
    print(f"\nverdict: {answer.verdict} ({answer.stage}, {time.monotonic() - t0:.1f}s)\n")
    print(answer.code)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
