# Floating-point mirror of the region-A check of RSBounds/HelfgottB6/Grid.lean (cellA, chkA),
# with the exact eta2DD (scipy sici) in place of the Taylor polynomial. Usage: python3 b6_region_a_check.py 28 90
import numpy as np, math, sys
from scipy.special import sici
def J(a,b,x):
    I1 = (sici(b*x)[1]-sici(a*x)[1]) - 1j*(sici(b*x)[0]-sici(a*x)[0])
    return (-np.exp(-1j*b*x)/b + np.exp(-1j*a*x)/a) - 1j*x*I1
def G(x):
    if x == 0: return 16-16-4+4*(4-2)-4*(2-1)
    return 16*np.exp(-1j*x/2)-16*np.exp(-1j*x/4)-4*np.exp(-1j*x)+4*J(.25,.5,x)-4*J(.5,1,x)
XA = float(sys.argv[1]); N = int(sys.argv[2])
err = 120*math.exp(N*math.log(XA) - math.lgamma(N+1))
print("err", err, "cond", XA/(N+1))
cnt = [0]
def chk(n, x0, x1):
    cnt[0] += 1
    if abs(G((x0+x1)/2)) + 12*(x1-x0) + err <= 31.521: return True
    if n == 0: return False
    xm = (x0+x1)/2
    return chk(n-1, x0, xm) and chk(n-1, xm, x1)
print("ok", chk(40, 0, XA), "cells", cnt[0])
