import mpmath as mp, time, json, sys

def delta_series(m, dps):
    mp.mp.dps = dps
    ln2 = mp.log(2)
    A = mp.mpf(0)
    for i in range(m+1):
        a = (m-i)*ln2
        s = mp.mpf(0); term = mp.mpf(1); n = 0
        while True:
            s += term / mp.mpf(n+1)**(i+1)
            n += 1
            term *= -a/n
            if n > 3*float(a) + 40 and abs(term) < mp.mpf(10)**(-dps):
                break
        A += mp.mpf(2)**i * s
    return A - mp.mpf(2)**(m+1) + ln2/4*mp.mpf(m)**2

out = {}
for m in [int(x) for x in sys.argv[1:]]:
    t0 = time.time()
    d = delta_series(m, 520)
    out[m] = mp.nstr(d, 20)
    print(f"m={m}  delta_m = {mp.nstr(d,20)}  ({time.time()-t0:.0f}s)", flush=True)
json.dump(out, open("delta_large.json", "w"), indent=1)
