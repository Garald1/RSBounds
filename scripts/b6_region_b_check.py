# Floating-point/exact-rational mirror of the region-B check of RSBounds/HelfgottB6/Grid.lean
# (cellB, chkB), used to choose K = 10 and W = 1/28. Usage: python3 b6_region_b_check.py 28 [exact]
# Region B check as it will be implemented in Lean (C2 via w1, no shifting).
import math, sys
from fractions import Fraction as Fr
K = 10; BOUND = Fr(31521, 1000)
RKc = 4*math.factorial(K)*(4**(K+1)-1)
# p_{k,n} as (re, im) integers: Phi_k(w) = sum_n p_{k,n} w^n
def ipow(n): return [(1,0),(0,1),(-1,0),(0,-1)][n % 4]
p = {1:[(0,0)]*(K+1), 2:[(0,0)]*(K+1), 4:[(0,0)]*(K+1)}
p[1][0] = (-16,0); p[2][0] = (16,0); p[4][0] = (-4,0)
for j in range(K):
    n = j+1; c = 4*math.factorial(n); ir, ii = ipow(n)
    p[2][n] = (c*2**(n+2)*ir, c*2**(n+2)*ii); p[1][n] = (-c*4**(n+1)*ir, -c*4**(n+1)*ii); p[4][n] = (-c*ir, -c*ii)
def cm(a, b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def ca(a, b): return (a[0]+b[0], a[1]+b[1])
def cs(c, a): return (c*a[0], c*a[1])
def ab1(a): return abs(a[0])+abs(a[1])
def ev(k, w):   # Phi_k(w), Phi_k'(w)
    v = (0,0); d = (0,0)
    for n in range(K, -1, -1):
        v = ca(cs(w, v), p[k][n])
    for n in range(K, 0, -1):
        d = ca(cs(w, d), cs(n, p[k][n]))
    return v, d
def C2(k, w1): return sum(Fr(n*(n-1), 2)*ab1(p[k][n])*w1**(n-2) for n in range(2, K+1))
def zm(m): d = 1+m*m; return ((1-m*m)/d, 2*m/d)
def cellB(s, m0, m1, w0, w1):
    mc = (m0+m1)/2; wc = (w0+w1)/2; ht = m1-m0; hw = (w1-w0)/2
    if 4*ht > 1: return False
    z1 = cs(s, zm(mc)); z2 = cm(z1, z1); z4 = cm(z2, z2); zs = {1:z1, 2:z2, 4:z4}
    F0=(0,0); Ft=(0,0); Fw=(0,0); E=0
    for k in (1,2,4):
        v, d = ev(k, wc)
        F0 = ca(F0, cm(v, zs[k])); Ft = ca(Ft, cs(k, cm(v, zs[k]))); Fw = ca(Fw, cm(d, zs[k]))
        E += ab1(v)*(k*ht)**2 + hw*ab1(d)*k*ht + C2(k, w1)*hw*hw
    M = BOUND - RKc*w1**K - E
    if M < 0: return False
    # conj(F0) * (i Ft): Re = Re(conj F0 * i Ft) = -(F0r*Fti... ) compute
    iFt = (-Ft[1], Ft[0])
    reA = F0[0]*iFt[0] + F0[1]*iFt[1]
    reB = F0[0]*Fw[0] + F0[1]*Fw[1]
    Q = F0[0]**2+F0[1]**2 + 2*ht*abs(reA) + 2*hw*abs(reB) + 2*ht*ht*(Ft[0]**2+Ft[1]**2) + 2*hw*hw*(Fw[0]**2+Fw[1]**2)
    return Q <= M*M
cnt = [0]
def chkB(n, s, m0, m1, w0, w1):
    cnt[0] += 1
    if cellB(s, m0, m1, w0, w1): return True
    if n == 0: return False
    if (m1-m0) >= (w1-w0):
        mm = (m0+m1)/2; return chkB(n-1, s, m0, mm, w0, w1) and chkB(n-1, s, mm, m1, w0, w1)
    ww = (w0+w1)/2; return chkB(n-1, s, m0, m1, w0, ww) and chkB(n-1, s, m0, m1, ww, w1)
exact = len(sys.argv) > 2
num = (lambda a, b: Fr(a, b)) if exact else (lambda a, b: a/b)
XB = int(sys.argv[1])
import time; t0 = time.time()
ok = chkB(60, 1, num(-1,1), num(1,1), num(0,1), num(1,XB)) and chkB(60, -1, num(-1,1), num(1,1), num(0,1), num(1,XB))
print("XB", XB, "exact" if exact else "float", "ok", ok, "cells", cnt[0], "time %.1fs" % (time.time()-t0))
