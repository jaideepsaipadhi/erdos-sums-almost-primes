#!/bin/bash
# Sharded delta-table extension m=1046..2440 across N cores.
# Run inside bm-rebuild-v21/ (needs delta_arb.py + existing delta_table.jsonl).
N=${1:-256}
MMAX=${2:-2440}
START=1046
echo "launching $N stride-shards for m=$START..$MMAX"
for ((r=0; r<N; r++)); do
    python3 delta_shard.py $START $N $r $MMAX &
done
wait
echo "all shards done; merging + verifying"
python3 merge_verify.py $MMAX
