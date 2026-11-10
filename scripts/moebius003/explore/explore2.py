import math, sys
import numpy as np
N=2**20
lam=np.zeros(N+1); isp=np.ones(N+1,bool); isp[:2]=False
for p in range(2,int(N**.5)+1):
    if isp[p]: isp[p*p::p]=False
for p in np.nonzero(isp)[0]:
    q=p
    while q<=N: lam[q]=math.log(p); q*=p
a=np.abs(lam-1); a[:2]=0
k=np.arange(N+1,dtype=float); k[0]=1
Gc=np.cumsum(a/k); Hc=np.cumsum(a/np.sqrt(k))
table=[2**s for s in range(1,21)]+[int(math.floor(10**(s/8)+1e-9)) for s in range(24,49)]
table=sorted(set(table))
X0=10**9; V=10**10; C5=0.0077629; cM=0.571; kap=6/math.pi**2
elo,ehi=0.96,1.17
I33=5.33; I0=I33+2*cM*(math.sqrt(X0)-math.sqrt(32)); C0=I0/math.log(X0)
I0=math.ceil(I0); C0=math.ceil(C0)
print("I0",I0,"C0",C0)
def cells_from_L(Ls):
    return [X0]+[int(round(math.exp(l))) for l in Ls[1:]]
Ls=[math.log(X0)]
h1=float(sys.argv[1]) if len(sys.argv)>1 else 0.5
h2=float(sys.argv[2]) if len(sys.argv)>2 else 0.69
Lend=float(sys.argv[3]) if len(sys.argv)>3 else 160
while Ls[-1]<Lend: Ls.append(min(Ls[-1]+(h1 if Ls[-1]<30 else h2),Lend))
D=cells_from_L(Ls)
n=len(D)-1
prev=[]; I=T=0.0; rows=[]
def etaMax(lo,hi):
    v=[e for (dl,dh,e) in prev if dl<=hi and lo<dh]
    return max(v) if v else 0.0
logV=math.log(V)
for i in range(n):
    Dm,Dp=D[i],D[i+1]; Lm,Lp=math.log(Dm),math.log(Dp); dl=1-Dm/Dp
    assert Dp<=2*Dm
    best=None
    for y in table:
        if not(1500<=y and 33*y<=Dm and y<=N): continue
        K=0.0; s=1
        while True:
            al=2**(s-1); be=min(2**s,y)
            lo=Dm//be; hi=(Dp-1)//max(al+1,2)
            w=0.0
            if lo<=X0: w+=cM*(Hc[be]-Hc[al])/math.sqrt(Dm)
            if hi>X0: w+=etaMax(max(lo,X0+1),hi)*(Gc[be]-Gc[al])
            K+=w
            if 2**s>=y: break
            s+=1
        lo=Dm//y; hi=(Dp-1)//y
        if lo<=X0: K+=0.8*cM/math.sqrt(Dm)
        if hi>X0: K+=0.8*etaMax(max(lo,X0+1),hi)/math.sqrt(y)
        J=1.6*kap/math.sqrt(y)+0.8*(4-kap+math.log(Dp/y+1))/math.sqrt(Dm)+kap/y+2/math.sqrt(Dm*y)+1/Dm
        if Dp>V:
            Jsq=kap*(math.log(Lp/logV)+2/logV**2)+(ehi-elo)/logV+elo/Lm
            J+=C5*Jsq
        X=1/Dm+K+J
        v=(X+(C0+I)/Dm)/(1-1/Lm-dl/Lm**2)
        if best is None or v<best[0]: best=(v,y,K,J)
    v,y,K,J=best
    e=v/Lm+(C0+I)/Dm+v*dl/Lm**2
    m=Lp*(e+max((I0+T)/Dm,(I0+T+e*(Dp-Dm))/Dp)+Lp/Dm)
    rows.append((i+1,Lm,Lp,y,K,J,v,e*Lm,m))
    prev.append((Dm,Dp,e))
    I+=v*(Dp-Dm)/Lm**2; T+=e*(Dp-Dm)
nus=[r[6] for r in rows]; ms=[r[8] for r in rows]
print("cells",n,"max nu %.5f at %d"%(max(nus),1+nus.index(max(nus))),"max m %.5f at %d"%(max(ms),1+ms.index(max(ms))))
i136=[r[0] for r in rows if r[2]>136]
print("max nu over cells with Lp>136: %.5f"%max(r[6] for r in rows if r[2]>136))
for r in rows[:5]+rows[20:26]+rows[-3:]: print("%3d %7.3f %7.3f %8d K=%.5f J=%.5f nu=%.5f etaL=%.5f m=%.5f"%r)
