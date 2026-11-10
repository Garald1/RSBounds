"""Numerical planning (not a proof): the project's eight-band b=23 budget with a
longer explicit zero head T0 in place of the first 29 zeros (T0 = 100).
Same formula as scripts/generate_quartic_budget_certificate.py, with
  0.592316 + lowIntegral(100) + (F(100)+R(100)-29)/100
replaced by
  S(T0) + lowIntegral(T0) + (F(T0)+R(T0)-N(T0))/T0,  S(T0) = sum_{0<gamma<=T0} 1/gamma.
"""
import sys
from mpmath import mp, mpf, log, pi
mp.dps = 40
zeros = []
for path in sys.argv[1:]:
    for line in open(path):
        if line.startswith('#') or not line.strip(): continue
        parts = line.split()
        zeros.append(mpf(parts[1]))
zeros = sorted(set(zeros))
twopi = 2*pi
def F(t): return t/twopi*(log(t/twopi)-1)+mpf(7)/8
def R(t): return mpf('0.137')*log(t)+mpf('0.443')*log(log(t))+mpf('1.588')
def J(t): return (log(t/twopi)/4+mpf(1)/16)/(twopi*t**4)+mpf('0.137')/(5*t**5)+mpf('0.443')/(5*t**5*log(t))
def budget(delta, T0, S0, N0, A=mpf(9472192561)/5000):
    a=1+2*delta; C=((1+delta)**5+1)**4/delta**4; Y=2/delta
    L,U=4/(3*delta),Y-8
    cut=[L+(U-L)*j/8 for j in range(9)]
    low=(log(Y/twopi)**2-log(T0/twopi)**2)/(4*pi)+mpf('0.137')*(1/T0-1/Y)+mpf('0.443')*(1/T0-1/Y)/log(T0)
    line=a*(S0+low+(F(T0)+R(T0)-N0)/T0)+C*J(Y)+2*R(Y)*(C/Y**5-a/Y)
    high=C*(J(A)+2*R(A)/A**5)
    mass=sum((F(v)-R(v)-F(u)-R(u))/v for u,v in zip(cut,cut[1:]))
    coeff=2*line-2*(a-mpf('0.931'))*mass
    return 2*delta+high+coeff/98715+(high+log(twopi)+mpf('0.1'))/mpf(98715)**2
def head(T0):
    g=[z for z in zeros if z<=T0]
    return sum(1/z for z in g), len(g)
S100,N100=head(100)
print(f"zeros loaded: {len(zeros)}, max ordinate {float(zeros[-1]):.3f}")
print(f"check: N(100)={N100}, S(100)={float(S100):.7f} (generator uses 0.592316)")
d0=mpf(211)/10**7
print(f"reproduce: T0=100 with S=0.592316 -> {float(budget(d0,mpf(100),mpf('0.592316'),29)):.12f}")
for T0 in [100,200,500,1000,2000,5000,10000]:
    S0,N0=head(T0)
    b=budget(d0,mpf(T0),S0,N0)
    # re-optimize delta on a grid
    best=min(((budget(mpf(dd)/10**8,mpf(T0),S0,N0),dd) for dd in range(1800,2500,5)))
    print(f"T0={T0:6d} N={N0:6d} S={float(S0):.6f}  budget(delta=2.11e-5)={float(b):.12f}  "
          f"best delta={best[1]/1e8:.3e} -> {float(best[0]):.12f}  {'<' if best[0]<mpf('0.00020171') else '>='} 0.00020171")
