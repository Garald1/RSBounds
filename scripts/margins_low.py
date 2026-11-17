# Floating-point margins for [H] (2.16), (2.18), (2.19) below 2e6 and the walk's own losses (docs/HelfgottLow.md).
import math, os, re
import numpy as np
N = 2_000_001
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
lam = np.zeros(N + 1)
for p in np.nonzero(sieve)[0]:
    lp = math.log(p); q = int(p)
    while q <= N:
        lam[q] = lp; q *= int(p)
n = np.arange(N + 1, dtype=float)
S16 = np.cumsum(lam * n); psi = np.cumsum(lam)
S18 = np.cumsum(np.where(n > 0, lam / np.sqrt(np.maximum(n, 1)), 0))
r = slice(663, 1600001)
rel16 = 1 - S16[r] / (1.03884 * n[r]**2 / 2); i = np.argmin(rel16)
print("(2.16) min relative slack on [663,1.6e6]: %.5f at n=%d" % (rel16[i], 663 + i))
print("(2.16) holds at 662?", S16[662] < 1.03884 * 662**2 / 2)
r = slice(2, 2000001)
rel18 = 1 - S18[r] / (2.0008 * np.sqrt(n[r])); i = np.argmin(rel18)
print("(2.18) min relative slack on [2,2e6]: %.5f at n=%d (abs %.3f)" % (rel18[i], 2 + i, (2.0008*np.sqrt(n[r])-S18[r])[i]))
lp2 = np.where(sieve, np.log(np.maximum(n, 1))**2, 0.0); Q = np.cumsum(lp2)
W = Q - Q[np.arange(N + 1) // 2]
rhs = n * np.log(np.maximum(n, 1)) / 2
r = slice(117, 2000001)
rel19 = 1 - W[r] / rhs[r]; i = np.argmin(rel19)
print("(2.19) min relative slack on [117,2e6]: %.5f at n=%d" % (rel19[i], 117 + i))
print("(2.19) holds at 116?", W[116] <= rhs[116])
N0 = 2_000_000
G = S18[N0] - psi[N0] / math.sqrt(N0)
print("G(N0) = %.4f, 1.0004 sqrt(N0) = %.4f, slack %.4f" % (G, 1.0004 * math.sqrt(N0), 1.0004 * math.sqrt(N0) - G))
# the walk's end values
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'RSBounds', 'HelfgottLow', 'States.lean')).read()
last = re.findall(r'\((2000001, [0-9, ]+)\)', src)[-1].split(', ')
SC = 10**15
psiW, tW = int(last[1]), int(last[3])
print("walk psi/SC - psi = %.3e, walk t/SC - S18 = %.3e" % (psiW / SC - psi[N0], tW / SC - S18[N0]))
RHO0 = 707106604409
print("walk bracket (SC t - RHO0 psi)/SC^2 = %.4f" % ((SC * tW - RHO0 * psiW) / SC**2))
