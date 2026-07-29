#!/usr/bin/env bash
# Self-healing certified run. Usage: ./runner.sh KMAX PREC
# Resumable: reruns only missing/truncated panels; safe to interrupt and restart.
set -u
KMAX=$1; PREC=$2
NPANEL=$(python3 -c "import math; print(math.ceil((3.5*$KMAX+5.1)/0.8))")
MEMK=$(awk '/MemAvailable/{print $2}' /proc/meminfo 2>/dev/null || echo 64000000)
W=$(( MEMK / 500000 )); C=$(nproc)
P=$(( W < C ? W : C )); P=$(( P < 1 ? 1 : P ))
echo "panels=$NPANEL  workers=$P (memory-capped from $C cores)"
for round in 1 2 3 4; do
  MISSING=$(python3 - <<PYEOF
import os
need = []
for i in range($NPANEL):
    fn = f"cchunks/c{i:04d}_{i+1:04d}.txt"
    ok = False
    if os.path.exists(fn):
        L = open(fn).read().splitlines()
        ok = (len(L) == $KMAX + 2 and L[0].startswith("#PARAMS")
              and "KMAX=$KMAX " in L[0]+" " and L[-1] == "#END")
    if not ok:
        need.append(i)
print(" ".join(map(str, need)))
PYEOF
)
  if [ -z "$MISSING" ]; then echo "all panels complete"; break; fi
  N=$(echo $MISSING | wc -w)
  echo "round $round: running $N panels"
  printf '%s\n' $MISSING | xargs -P $P -I{} bash -c "python3 certified.py $KMAX $PREC {} \$(({}+1)) 2>/dev/null"
done
python3 certificate.py $KMAX $PREC
