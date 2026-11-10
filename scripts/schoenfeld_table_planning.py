# Planning numerics only (not a proof). A far-only m-th order smoothing envelope split at A = 1894439:
# eps_m(b) = min over delta of m*delta/2 + (R_m(delta)/delta^m) * [far zeros above A via the zero-free region, using
# SchoenfeldLaplaceTails.farPrimitive and Phi at general m] + a crude critical-line term. Compares with the 1976 table (p. 358).
# R_m(delta) = ((1+delta)^(m+1)+1)^m generalizes QuadraticZeroKernel.R2 and PolynomialZeroKernel.R4. Needs mpmath.
# Planning numerics only: far-only m-th order envelope with split at A (no near region).
from mpmath import mp, mpf, log, exp, sqrt, pi, findroot
mp.dps = 30
R = mpf('9.645908801'); A = mpf(1894439); d = log(mpf(17)/(2*pi)); uA = log(A/17)
def rosserR(t): return mpf('0.137')*log(t) + mpf('0.443')*log(log(t)) + mpf('1.588')
def q(t): return (mpf('0.137') + mpf('0.443')/log(t))/(t*log(t/(2*pi)))
def farPrim(a, m, u): return (u + d + mpf(1)/m)*u**2/(m*u**2 - a)*exp(-(m*u + a/u))
def Phi(a, m, t): return exp(-a/log(t/17))/t**(m+1)
def F(b, m):
    a = b/R
    return (1/(2*pi) + q(A))*farPrim(a, m, uA)/mpf(17)**m + 2*rosserR(A)*Phi(a, m, A)
def Rm(m, dl): return ((1+dl)**(m+1) + 1)**m
def eps(b, m):
    f = F(b, m)
    best = None
    dl = mpf('1e-7')
    while dl < mpf('0.01'):
        e = m*dl/2 + Rm(m, dl)/dl**m*f + Rm(m,dl)/dl**m*exp(-b/2)*mpf('0.0463')/mpf('14.13')**(m-1)
        if best is None or e < best[0]: best = (e, dl)
        dl *= mpf('1.02')
    return best
table = {400:1.3548e-5, 550:1.1854e-5, 650:1.0748e-5, 700:1.0196e-5, 750:9.6493e-6, 800:9.1328e-6,
         850:8.5876e-6, 900:8.0655e-6, 950:7.5754e-6, 1000:7.0481e-6, 1050:6.5529e-6, 1150:5.6055e-6,
         1350:3.8789e-6, 1650:1.9368e-6, 1700:1.6887e-6}
print("b      table      m=2        m=3        m=4        m=5        m=6")
for b in [50, 100, 200, 300, 400, 550, 650, 800, 1000, 1150, 1350, 1500, 1650, 1700, 1737]:
    row = [f"{b:5d}", f"{table.get(b, float('nan')):.4e}"]
    for m in [2,3,4,5,6]:
        row.append(f"{float(eps(mpf(b), m)[0]):.4e}")
    print("  ".join(row))
