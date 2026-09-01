#!/bin/bash
# extra_hard family, latency profile, Lean-checked, LLM armed.
cd "$(dirname "$0")/../.."
set -a; source ~/.sair_env; set +a
OUT=artifacts/bench-latency-extrahard
for k in 0 1 2 3; do
  python3 scripts/bench.py artifacts/problems/stage2_stress_200.jsonl $OUT --shard $k/4 --llm --profile latency --only order4_extra_hard > $OUT/shard-$k.log 2>&1 &
done
wait
python3 scripts/bench.py --report $OUT > /dev/null
echo done
