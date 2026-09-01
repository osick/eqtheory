#!/bin/bash
# 4 shards, self-contained certificates (v0.2.0), Lean found via elan, LLM armed.
cd "$(dirname "$0")/../.."
set -a; source ~/.sair_env; set +a
OUT=artifacts/bench-stress-2026-09-01-standalone
for k in 0 1 2 3; do
  python3 scripts/bench.py artifacts/problems/stage2_stress_200.jsonl $OUT --shard $k/4 --llm > $OUT/shard-$k.log 2>&1 &
done
wait
python3 scripts/bench.py --report $OUT > /dev/null
echo done
