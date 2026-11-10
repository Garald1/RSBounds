import math
C5=0.0077629; kap=6/math.pi**2; C0=1743; elo,ehi=0.96,1.17
lam0=1.1069
def Phi(L,th,nuinf,nubar):
    l=th*L; D=math.exp(L); y=math.exp(l)
    ks=2*nuinf*math.log(L/(L-l))+2*nubar*lam0*(1/(L-l)-1/L)+2*C0*y/D
    bd=C5*(C0*y/(l*D)+nuinf/(l*(L-l))+nubar*lam0/(l*(L-l)**2))
    js=C5*(kap*math.log(L/l)+2*kap/l**2+(ehi-elo)/l+elo/L)+kap/y+(2*math.sqrt(D/y)+1)/D
    return ((1+C0)/D+nubar*lam0/L**2+ks+bd+js)/(1-1/L)
for th in [0.13,0.14,0.15,0.16]:
    print(th, Phi(160,th,0.014,0.017), Phi(160,th,0.0135,0.017))
# Cor 11
def cor11(L,nuinf,nubar,c=3):
    return nuinf*(1+L/(L-c))+nubar*lam0*(1+lam0)/L
print("cor11",cor11(160,0.014,0.017),cor11(160,0.014,0.017,2))
