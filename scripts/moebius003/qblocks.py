import math
T=10**4
mu2=[0]*(T+1)
for n in range(1,T+1):
    ok=True; d=2
    while d*d<=n:
        if n%(d*d)==0: ok=False;break
        d+=1
    mu2[n]=1 if ok else 0
Q1=[0.0]*(T+1)
for n in range(1,T+1): Q1[n]=Q1[n-1]+mu2[n]/n
klo,khi=0.6079267,0.6079274
eLo,eHi=0.96,1.17
def ok(a,b): return Q1[a+1]-khi*math.log(b)>=eLo+1e-4 and Q1[b]-klo*math.log(a+1)<=eHi-1e-4
blocks=[0]; a=0
while a<T:
    b=a+1
    if not ok(a,b): raise Exception("fail at %d"%a)
    while b<T and ok(a,b+1): b+=1
    blocks.append(b); a=b
print(len(blocks), blocks[:40], blocks[-5:])
ET=Q1[T]-0.6079271018540267*math.log(T); print("E(T)",ET)
open("qblocks.txt","w").write(",".join(map(str,blocks)))
