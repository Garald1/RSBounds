#!/usr/bin/env python3
"""Independent floating-point cross-check (50-digit decimal arithmetic), not used by the proof.

Recomputes A(n), G(N), H(N) directly from a sieve and Decimal logarithms and reports
* the minimal relative margin of A(n) <= 2(n-1) over 2 <= n <= 2^20;
* the minimal distance (in units of 1e-6) between the ghTable bounds and G, H.
Usage (from the project root):  python3 tools/reference_check.py
"""
import os, re
from decimal import Decimal, getcontext
getcontext().prec = 50
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
N = 1 << 20
spf = list(range(N + 1))
for i in range(2, int(N**0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, N + 1, i):
            if spf[j] == j: spf[j] = i
logs = {}
def a(k):
    p = spf[k]; m = k
    while m % p == 0: m //= p
    if m != 1: return Decimal(1)
    if p not in logs: logs[p] = Decimal(p).ln()
    return abs(logs[p] - 1)
tab = open(os.path.join(ROOT, "RSBounds/LambdaInputs.lean")).read()
rows = [tuple(map(int, e)) for e in re.findall(r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", tab)]
want = {r[0] for r in rows}
A = G = H = Decimal(0); worst = (Decimal(10), None); val = {}
for k in range(2, N + 1):
    ak = a(k); A += ak; G += ak / k; H += ak / Decimal(k).sqrt()
    r = 1 - A / (2 * (k - 1))
    if r < worst[0]: worst = (r, k)
    if k in want: val[k] = (G, H)
print("min relative margin of A(n) <= 2(n-1):", worst[0], "at n =", worst[1])
md = min(min(val[n][0] * 10**6 - gl, gh - val[n][0] * 10**6, val[n][1] * 10**6 - hl, hh - val[n][1] * 10**6)
         for (n, gl, gh, hl, hh) in rows)
print("min distance of a ghTable bound from the value, in units of 1e-6:", md)
print("G(2^20) =", val[N][0]); print("H(2^20) =", val[N][1])
