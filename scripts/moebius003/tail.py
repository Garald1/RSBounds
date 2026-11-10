import math
C5=0.0077629; kHi=0.6079274; C0B=1743; I0B=36113; lam0=1.107
nub=0.017; nui=0.014; th=0.15; L0=160.0; d0=1e-9
l0=th*L0-d0
Dend=306985e64
T = (1+C0B)/Dend + nub*lam0/L0**2 + 2*nui*math.log(20/17) + 2*nub*lam0*(th/(1-th))/L0 + 2*C0B*math.exp(-136)
T += C5*(C0B*math.exp(-136)/l0 + nui/(l0*136) + nub*lam0/(l0*136**2))
T += C5*(kHi*(math.log(1/(th-d0/L0)) + 2/l0**2) + 0.21/l0 + 0.96/L0) + kHi/(math.exp(24)-1) + 2/math.sqrt(Dend) + 1/Dend
print("Phi bracket", T, "need <=", nui*(1-1/L0), "margin", nui*(1-1/L0)-T)
# Cor 11
Le=160.0000002
cor = (C0B/Dend + nui/L0 + nub*lam0/L0**2 + (I0B + C0B*Le + nub*942467e53/20)/Dend + nui/(L0-2) + nub*lam0**2/L0**2 + Le/Dend)*(Le+1/Dend)
print("Cor11", cor)
