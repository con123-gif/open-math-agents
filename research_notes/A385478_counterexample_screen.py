"""Exact bounded screening of the literal A385478 conjecture; no infinite claim."""
from array import array
from pathlib import Path
import json, time

N = 300_000
started = time.monotonic()
sigma = array('I', [0]) * (N + 1)
for d in range(1, N + 1):
    for n in range(d, N + 1, d):
        sigma[n] += d
M = max(sigma)
spf = array('I', range(M + 1))
for p in range(2, int(M**0.5) + 1):
    if spf[p] == p:
        for v in range(p*p, M + 1, p):
            if spf[v] == v:
                spf[v] = p
seen = bytearray(M + 1)
first = array('I', [0]) * (M + 1)
for n in range(1, N + 1):
    t = sigma[n]
    divisors = [1]
    while t > 1:
        p, pw = spf[t], 1
        base = divisors[:]
        while t % p == 0:
            t //= p
            pw *= p
            divisors += [x*pw for x in base]
    new = sorted(d for d in divisors if not seen[d])
    if new:
        a = new[0]
        bad = [d for d in new if d % a]
        if bad:
            result = dict(status='counterexample', n=n, sigma=int(sigma[n]),
                          least_new=a, new=new, bad=bad,
                          previous_first={str(d):int(first[d]) for d in divisors},
                          seconds=time.monotonic()-started)
            break
    for d in divisors:
        if not seen[d]:
            first[d] = n
            seen[d] = 1
else:
    result = dict(status='no_counterexample_in_finite_range', N=N,
                  max_sigma=int(M), seconds=time.monotonic()-started)
Path('number_work/A385478_COUNTEREXAMPLE_SCREEN.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
