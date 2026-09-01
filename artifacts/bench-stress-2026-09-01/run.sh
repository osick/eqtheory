#!/bin/bash
# 4 shards (box rule: ≤4 Lean judges at once), Lean-checked, LLM armed.
cd "$(dirname "$0")/../.."
set -a; source ~/.sair_env; set +a
export EQTHEORY_LEAN_BIN=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean
export EQTHEORY_JUDGE_ROOT=$PWD/../info/equational-theories-lean-stage2
OUT=artifacts/bench-stress-2026-09-01
for k in 0 1 2 3; do
  python3 scripts/bench.py ../tests/manifests/stage2_stress_test.jsonl $OUT --shard $k/4 --llm > $OUT/shard-$k.log 2>&1 &
done
wait
python3 scripts/bench.py --report $OUT > /dev/null
echo done
