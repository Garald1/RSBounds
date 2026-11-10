# Numerical margin study for the Theorem 11 parameter balance on the exact formal envelope
# of SchoenfeldQuadraticLeft.psi_error_le_envelope. Planning aid only; not a proof. Needs mpmath.
# Ratio (formal |psi-x| bound)/(x*eps0(x)) for the exact envelope in SchoenfeldQuadraticLeft.psi_error_le_envelope.
from mpmath import mp, mpf, exp, log, sqrt, pi, findroot
mp.dps = 50
R = mpf("9.645908801"); d = log(mpf(17) / (2 * pi))
def E_over_eps0(X, v, delta):
    a, u = X**2, v * X
    U = 17 * exp(u); logx = R * X**2
    q = (mpf("0.137") + mpf("0.443") / log(U)) / (U * log(U / (2 * pi)))
    rR = mpf("0.137") * log(U) + mpf("0.443") * log(log(U)) + mpf("1.588")
    near = u**2 * (u + d) / a * exp(-a / u) / (2 * pi) + 2 * rR * exp(-a / u) / U
    far = (1 / (2 * pi) + q) * (u + d + mpf(1) / 2) * u**2 / (2 * u**2 - a) * exp(-(2 * u + a / u)) / 289 \
          + 2 * rR * exp(-a / u) / U**3
    R2 = ((1 + delta)**3 + 1)**2
    E = (R2 / delta**2) * (mpf("0.0463") / mpf("14.13")) * exp(-logx / 2) + (1 + delta) * near \
        + (R2 / delta**2) * far + 150000 / delta**2 * exp(-mpf("1.5") * logx) + log(2 * pi) * exp(-logx) + delta
    eps0 = sqrt(mpf(8) / (17 * pi)) * sqrt(X) * exp(-X)
    return E / eps0
def best(X):
    # crude 2-D search over v in (1/sqrt2, 1], delta > 0 (log grid), then local refine
    from mpmath import mpf as F
    bestv = None
    for i in range(1, 400):
        v = F(1) / sqrt(2) + (1 - F(1) / sqrt(2)) * F(i) / 400
        if v * X < log(F(1894439) / 17): continue
        for j in range(-40, 1):
            delta = sqrt(F(8) / (17 * pi)) * sqrt(X) * exp(-X) * F(2) ** (F(j) / 8)
            r = E_over_eps0(X, v, delta)
            if bestv is None or r < bestv[0]: bestv = (r, v, delta)
    return bestv
for L in [1737, 1800, 2000, 3000, 5000, 20000, 100000]:
    X = sqrt(L / R)
    r, v, delta = best(X)
    print(f"log x = {L:6d}  X = {float(X):8.3f}  best ratio = {float(r):.6f}  at v = {float(v):.4f}, delta/eps0 = {float(delta/(sqrt(mpf(8)/(17*pi))*sqrt(X)*exp(-X))):.4f}")

print("--- Schoenfeld's choices: v solves k(v)=1 (7.27); delta from (7.24a) ---")
def k_minus_1(X, v):
    G0 = v**2 * (v + d / X)
    G1 = v**2 * (v + (1 + 2 * d) / (2 * X)) / (2 * v**2 - 1)
    return 17 * X / (2 * pi) * sqrt(G0**3 / G1) * exp(-2 * X * (1 - v)) * exp(-X * (1 - v)**2 / v) - 1
for L in [1737, 2000, 5000, 1e5, 1e7, 1e9, 1e12]:
    X = sqrt(mpf(L) / R)
    v0 = 1 - log(17 * X / (2 * pi)) / (2 * X); v1 = 1 - log(17 * X / (5 * pi)) / (2 * X)
    v = findroot(lambda t: k_minus_1(X, t), (v0, v1), solver="anderson")
    G0 = v**2 * (v + d / X); G1 = v**2 * (v + (1 + 2 * d) / (2 * X)) / (2 * v**2 - 1)
    Y = X * (1 - v)**2 / v
    delta = (G0 * G1)**(mpf(1) / 4) * exp(-Y / 2) * sqrt(mpf(2) / (17 * pi)) * sqrt(X) * exp(-X)
    print(f"log x = {float(L):10.4g}  v0={float(v0):.5f} v={float(v):.5f} v1={float(v1):.5f}  ratio = {float(E_over_eps0(X, v, delta)):.6f}   1-ratio = {float(1-E_over_eps0(X, v, delta)):.3e}")
