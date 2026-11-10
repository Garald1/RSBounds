import math
def f(a,b): return math.log(b+1)*(3*0.571/math.sqrt(a)+math.log(b)/a)
pts=[600001]; a=600001
while a<10**9:
    # binary search largest b with f(a,b)<=0.03-2e-6
    lo,hi=a,10**9
    if f(a,a)>0.03-2e-6: raise Exception("fail %d"%a)
    while lo<hi:
        mid=(lo+hi+1)//2
        if f(a,mid)<=0.03-2e-6: lo=mid
        else: hi=mid-1
    b=lo
    pts.append(b); a=b
print(len(pts)-1, pts[:10], pts[-3:])
open("range2.txt","w").write(",".join(map(str,pts)))
