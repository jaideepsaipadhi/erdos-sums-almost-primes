"""Contiguous certified delta_m table. Adaptive precision: prec ~ 2.2*m + 300 bits
(0.6*m digits of cancellation + guard). Appends to delta_table.jsonl, resumable."""
import sys, os, time, json
from delta_arb import delta_arb

def main(m_lo, m_hi):
    path = "/home/claude/delta_table.jsonl"
    done = set()
    if os.path.exists(path):
        for line in open(path):
            done.add(json.loads(line)["m"])
    with open(path, "a") as fh:
        t0 = time.time()
        for m in range(m_lo, m_hi + 1):
            if m in done:
                continue
            prec = int(2.2 * m) + 300
            d = delta_arb(m, prec)
            rec = {"m": m, "mid": d.mid().str(30), "rad": d.rad().str(5), "prec": prec}
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            if m % 50 == 0:
                print(f"m={m} done ({time.time()-t0:.0f}s elapsed)", flush=True)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
