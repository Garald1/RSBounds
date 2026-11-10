"""Planning (not a proof): 4*pi*G(D) of Schoenfeld 1976, (8.5) p. 351, and S(D) of (8.6), from candidate zero ordinates (argument: a zeros file such as zeta-zero-locations data/zeros_T10000.txt)."""
import sys
from mpmath import mp, mpf, log, pi, sqrt
mp.dps = 30
z = sorted({mpf(l.split()[1]) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')})
def G(D):
    g = [t for t in z if t <= D]
    S = sum(1/sqrt(t*t + mpf(1)/4) for t in g)
    G = S - ((log(D/(2*pi)) - 1)**2 + 1)/(4*pi) + (mpf('0.137')*log(D) + mpf('0.443')*(log(log(D)) + 1/log(D)) + mpf('2.6') - len(g))/D
    return len(g), S, 4*pi*G
print(f"{'D':>12} {'N(D)':>6} {'S(D)':>12} {'4piG(D)':>11}")
for D in ['100', '158.84998', '500', '1000', '2000', '5000', '7436.76651', '8929.80867', '10000']:
    n, S, g = G(mpf(D))
    print(f"{D:>12} {n:>6} {float(S):12.8f} {float(g):11.6f}")
