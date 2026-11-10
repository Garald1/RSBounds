# Planning numerics only (not a proof). Ratio of the exact formal quadratic envelope
# (SchoenfeldQuadraticLeft.psi_error_le_envelope) to x*eps0(x) below log x = 1737, choosing v >= log(A/17)/X
# (so that U >= A) and delta per x. Run from the project root; reuses scripts/schoenfeld_balance_margin.py.
import sys, importlib.util
sys.argv = ['x']
src = open('scripts/schoenfeld_balance_margin.py').read().split('for L in [1737')[0]
exec(src)
from mpmath import mpf, sqrt, log, exp, pi
uA = log(mpf(1894439)/17)
def best_delta(X, v):
    b = None
    eps0 = sqrt(mpf(8)/(17*pi))*sqrt(X)*exp(-X)
    for j in range(-120, 40):
        delta = eps0 * mpf(2)**(mpf(j)/16)
        r = E_over_eps0(X, v, delta)
        if b is None or r < b[0]: b = (r, delta/eps0)
    return b
def eps0L(L):
    X = sqrt(mpf(L)/R); return sqrt(mpf(8)/(17*pi))*sqrt(X)*exp(-X)
print(" log x     X      v=uA/X   best ratio (bound/eps0(x))   bound/eps0(e^(L+50))")
for L in [1303, 1310, 1325, 1350, 1400, 1450, 1500, 1550, 1600, 1650, 1700, 1737]:
    X = sqrt(mpf(L)/R)
    v = uA/X
    if v > 1: print(L, "window fails"); continue
    # also allow larger v (U above A) up to 1
    bestr = None
    for i in range(0, 41):
        vv = v + (1 - v)*mpf(i)/40
        r, dd = best_delta(X, vv)
        if bestr is None or r < bestr[0]: bestr = (r, vv, dd)
    r, vv, dd = bestr
    print(f"{L:6d} {float(X):7.3f}  {float(v):.4f}  ratio={float(r):.4f} at v={float(vv):.4f}   next50: {float(r*eps0L(L)/eps0L(L+50)):.4f}")
