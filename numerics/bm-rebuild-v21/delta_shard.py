"""Stride-sharded certified delta table worker.
Usage: python3 delta_shard.py START STRIDE OFFSET MMAX
Computes delta_m for m = START+OFFSET, START+OFFSET+STRIDE, ... <= MMAX,
writing shard_OFFSET.jsonl (resumable: skips m already present in its shard).
Stride sharding balances load across cores despite ~m^3 per-value cost."""
import sys, os, json, time
from delta_arb import delta_arb

def main(start, stride, offset, mmax):
    path = f"shards/shard_{offset:04d}.jsonl"
    os.makedirs("shards", exist_ok=True)
    done = set()
    if os.path.exists(path):
        for line in open(path):
            done.add(json.loads(line)["m"])
    with open(path, "a") as fh:
        for m in range(start + offset, mmax + 1, stride):
            if m in done:
                continue
            prec = int(2.2 * m) + 300
            d = delta_arb(m, prec)
            fh.write(json.dumps({"m": m, "mid": d.mid().str(30), "rad": d.rad().str(5), "prec": prec}) + "\n")
            fh.flush()

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
