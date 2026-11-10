"""Planning numerics (not a proof): rows of the order-6 far-only envelope for (5.6b*) on
[e^313, e^947], with the constants of Schoenfeld1976Rows6.row6:

    eps = 3*delta + (64 + 2800*delta)/delta^6 * En * W6(bh) + 1e-20,
    W6(bh) = 0.16*12.793*135.26/((800.41 - bh/R) * A^6) + 20/A^7,
    En >= exp(-(bl/R/11.63)),   eps*bh < 0.0077629.

En is taken as 1/L with L = 2.7182818283^n * (1 + f + f^2/2 + f^3/6) <= e^(n+f), n + f <= bl/R/11.63
(the form Schoenfeld1976Rows2.exp_neg_le proves). Prints Lean-ready parameters.
"""
from fractions import Fraction as Fr
import math
R = 9.645908801; A = 1894439
def W6(bh): return 0.16*12.793*135.26/((800.41 - bh/R)*A**6) + 20/A**7
def eps(bl, bh, dl, En): return 3*dl + (64 + 2800*dl)/dl**6*En*W6(bh) + 1e-20
def En_for(bl):
    y = bl/R/11.63
    n = int(math.floor(y)); f = math.floor((y - n)*1000)/1000
    L = 2.7182818283**n*(1 + f + f**2/2 + f**3/6)
    L = math.floor(L*1000)/1000   # round down
    return n, f, L
def best(bl, bh):
    n, f, L = En_for(bl); En = 1/L
    b = min((eps(bl, bh, d*1e-9, En), d*1e-9) for d in range(500, 20000, 1))
    return b, (n, f, L)
rows = []; bl = 313
while bl < 947:
    lo, hi = bl + 1, 947
    ok = None
    for bh in range(hi, lo - 1, -1):
        (e, dl), en = best(bl, bh)
        if e*bh < 0.0077629*(1 - 2e-4):
            ok = (bh, e, dl, en); break
    if ok is None: raise SystemExit(f"stuck at {bl}")
    bh, e, dl, en = ok
    rows.append((bl, bh, e, dl, en)); bl = bh
for bl, bh, e, dl, (n, f, L) in rows:
    print(f"[{bl},{bh}] delta={dl:.3e} eps={e:.4e} eps*bh={e*bh:.6f} En=1/{L} (n={n}, f={f})")
