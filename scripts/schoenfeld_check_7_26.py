# Planning aid, not a proof: compares the exact formal envelope terms with Schoenfeld (7.26). Needs mpmath.
# Check: formal (1+delta)*near + (R2/delta^2)*far + delta  <  Schoenfeld's (7.26) right side, with v: k(v)=1, delta (7.24a).
from mpmath import mp, mpf, exp, log, sqrt, pi, findroot
mp.dps = 50
R = mpf("9.645908801"); d = log(mpf(17) / (2 * pi))
for L in [1737, 3000, 1e5, 1e9]:
    X = sqrt(mpf(L) / R)
    G0 = lambda v: v**2 * (v + d / X)
    G1 = lambda v: v**2 * (v + (1 + 2 * d) / (2 * X)) / (2 * v**2 - 1)
    kk = lambda v: 17 * X / (2 * pi) * sqrt(G0(v)**3 / G1(v)) * exp(-2 * X * (1 - v)) * exp(-X * (1 - v)**2 / v) - 1
    v = findroot(kk, (1 - log(17*X/(2*pi))/(2*X), 1 - log(17*X/(5*pi))/(2*X)), solver="anderson")
    g0, g1, Y = G0(v), G1(v), X * (1 - v)**2 / v
    delta = (g0 * g1)**(mpf(1)/4) * exp(-Y/2) * sqrt(2/(17*pi)) * sqrt(X) * exp(-X)
    T2 = 17 * exp(v * X)
    q = (mpf("0.137") + mpf("0.443") / log(T2)) / (T2 * log(T2 / (2 * pi)))
    rR = mpf("0.137") * log(T2) + mpf("0.443") * log(log(T2)) + mpf("1.588")
    u, a = v * X, X**2
    near = u**2*(u+d)/a*exp(-a/u)/(2*pi) + 2*rR*exp(-a/u)/T2
    far = (1/(2*pi)+q)*(u+d+mpf(1)/2)*u**2/(2*u**2-a)*exp(-(2*u+a/u))/289 + 2*rR*exp(-a/u)/T2**3
    R2 = ((1 + delta)**3 + 1)**2
    lhs = (1 + delta) * near + R2 / delta**2 * far + delta
    G2 = R2 / 4 * (1 + 2 * pi * q)
    rhs = G2 * (g0*g1)**(mpf(1)/4) * exp(-Y/2) * sqrt(8/(17*pi)) * sqrt(X) * exp(-X) + mpf("0.0482") * G2 * (1 + g0/g1) * exp(-Y) * X * exp(-2*X)
    # identity check for (7.24b): T2 should equal (G1/G0^3)^(1/4) e^{Y/2} sqrt(34 pi) X^{-1/2} e^X
    T2b = (g1 / g0**3)**(mpf(1)/4) * exp(Y/2) * sqrt(34*pi) / sqrt(X) * exp(X)
    print(f"log x={float(L):8.3g}: lhs/rhs = {float(lhs/rhs):.6f}   T2/T2(7.24b) = {float(T2/T2b):.12f}")
