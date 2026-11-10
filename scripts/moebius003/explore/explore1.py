import math
from fractions import Fraction as F
def mobius_list(n):
    mu=[1]*(n+1); mu[0]=0
    isp=[True]*(n+1); isp[0]=isp[1]=False
    for p in range(2,n+1):
        if isp[p]:
            for q in range(2*p,n+1,p): isp[q]=False
            for q in range(p,n+1,p): mu[q]*=-1
            for q in range(p*p,n+1,p*p): mu[q]=0
    return mu
mu=mobius_list(10**5)
M=[0]*(10**5+1)
for i in range(1,10**5+1): M[i]=M[i-1]+mu[i]
print("M(1..32)=",M[1:33])
S33=sum(abs(M[t])*math.log(1+1/t) for t in range(1,33)); S33b=sum(F(abs(M[t]),t) for t in range(1,33))
print("S33 log",S33," S33 1/t",float(S33b), S33b)
kap=6/math.pi**2
Q1=0;Emin=9;Emax=-9;argmin=argmax=0
for i in range(1,10**5+1):
    Q1+= (1 if mu[i]!=0 else 0)/i
    E=Q1-kap*math.log(i)
    if E<Emin: Emin,argmin=E,i
    if E>Emax: Emax,argmax=E,i
    if i==10**4: print("E(1e4)=",E)
print("integer inf E",Emin,argmin," sup",Emax,argmax)
print("kappa",kap, 1/(1-2/math.log(1e9)))
