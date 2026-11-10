import mpmath, json
mpmath.mp.dps=100
X0=10**9
Ls=[mpmath.log(X0)]
while Ls[-1]<160:
    h=mpmath.mpf('0.5') if Ls[-1]<30 else mpmath.mpf('0.69')
    Ls.append(min(Ls[-1]+h,mpmath.mpf(160)))
def round6(v, up=False):
    v=mpmath.mpf(v); d=int(mpmath.floor(mpmath.log10(v)))+1
    k=max(0,d-6)
    q=v/mpmath.mpf(10)**k
    c=int(mpmath.ceil(q)) if up else int(mpmath.nint(q))
    return c*10**k
D=[X0]+[round6(mpmath.e**l) for l in Ls[1:-1]]+[round6(mpmath.e**Ls[-1],up=True)]
assert all(D[i+1]<=2*D[i] and D[i+1]>D[i] for i in range(len(D)-1))
assert D[-1]>=mpmath.e**160
mid=max(d for d in D if d<=mpmath.e**(mpmath.mpf('0.85')*mpmath.log(D[-1])))
print(len(D)-1,"cells; Dend=",D[-1]," log Dend=",mpmath.nstr(mpmath.log(D[-1]),12))
print("Dmid index",D.index(mid),"log Dmid",mpmath.nstr(mpmath.log(mid),12), mid)
json.dump({"D":[str(d) for d in D],"Dmid":str(mid)},open("endpoints.json","w"))
