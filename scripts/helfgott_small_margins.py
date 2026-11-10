# Numerical margins (floating point, not a proof) for [H] (2.14) and (2.17) below the ranges
# already proved in RSBounds.  (2.14): psi(y) <= 1.0004 y for y >= 2e6.  (2.17): S(y) = sum_{n<=y}
# Lambda(n) n < 1.0008 y^2/2 for y > 1.6e6.  Both sides are step-vs-increasing, so the worst points
# are the prime powers q (just at the jump) and the left endpoints.
import numpy as np, math
N = 25_000_000
s = np.ones(N + 1, dtype=bool); s[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if s[p]: s[p*p::p] = False
primes = np.nonzero(s)[0]
lam = np.zeros(N + 1)
lp = np.log(primes.astype(np.float64))
lam[primes] = lp
for p, l in zip(primes[primes <= int(N ** 0.5) + 1], lp):
    q = p * p
    while q <= N:
        lam[q] = l; q *= p
psi = np.cumsum(lam)
S = np.cumsum(lam * np.arange(N + 1, dtype=np.float64))
pp = np.nonzero(lam)[0]
# (2.14) on [2e6, 4e6]
a, b = 2_000_000, 4_000_000
q = pp[(pp > a) & (pp <= b)]
m14 = np.concatenate(([psi[a] - 1.0004 * a], psi[q] - 1.0004 * q))
pts = np.concatenate(([a], q))
i = np.argmax(m14)
print(f"(2.14) on [2e6,4e6]: max psi(y) - 1.0004y = {m14[i]:.3f} at y = {pts[i]}  (needs < 0)")
d = psi[pts] - pts
print(f"        max psi(y) - y there = {d.max():.3f}; min margin 0.0004y-(psi-y) = {(-m14).min():.3f}")
# where would (2.14) first hold from? scan down from 2e6
qq = pp[pp <= a]; bad = qq[psi[qq] > 1.0004 * qq]
print(f"        largest prime power q <= 2e6 with psi(q) > 1.0004 q: {bad.max() if len(bad) else None}")
# (2.17) on (1.6e6, 2.5e7]
a, b = 1_600_000, N
q = pp[(pp > a) & (pp <= b)]
m17 = np.concatenate(([S[a] - 1.0008 * a * a / 2], S[q] - 1.0008 * q.astype(np.float64) ** 2 / 2))
pts = np.concatenate(([a], q))
i = np.argmax(m17)
print(f"(2.17) on (1.6e6,2.5e7]: max S(y) - 1.0008y^2/2 = {m17[i]:.4g} at y = {pts[i]} (needs < 0)")
rel = m17 / (pts.astype(np.float64) ** 2 / 2)
print(f"        relative: max (S - 1.0008 y^2/2)/(y^2/2) = {rel.max():.3e}  i.e. margin {-rel.max():.3e} of y^2/2")
qq = pp[pp <= a]; bad = qq[S[qq] >= 1.0008 * qq.astype(np.float64) ** 2 / 2]
print(f"        largest prime power q <= 1.6e6 with S(q) >= 1.0008 q^2/2: {bad.max() if len(bad) else None}")
