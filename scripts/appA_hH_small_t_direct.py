# Cross-check h_H(t) at tiny t from the definition: h_H(t) = int_0^2 h'(u) G_H(log(t/u)) du, G_H(z) = Si(Hz)/pi
import numpy as np
from scipy.special import sici
from scipy.integrate import quad
H = 200.0
def hp(u): return np.exp(u-0.5)*u*(2-u)**2*(1-u)*(4+u)
for L in [-10.0, -20.0, -40.0]:
    t = np.exp(L)
    # G_H(log(t/u)) + 1/2 (since sum of h' over [0,2] is 0, adding 1/2 changes nothing); oscillatory: integrate in v = log u
    f = lambda v: hp(np.exp(v)) * np.exp(v) * (sici(H*(L - v))[0]/np.pi + 0.5)
    pts = np.linspace(-30, np.log(2), 4001)
    tot = sum(quad(f, a, b, limit=200, epsabs=1e-16, epsrel=1e-10)[0] for a, b in zip(pts[:-1], pts[1:]))
    print("t=e^%g  h_H(t) = %.4e   |h_H - h|/t ~ %.3e" % (L, tot, abs(tot)/t))
