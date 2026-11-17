# h_H(e^L) = int_{|xi| <= H/2pi} e(xi L) ghat(xi) dxi, g(u) = h(e^u); check |h_H(t) - h(t)|/t for tiny t
import numpy as np
from scipy.integrate import quad
H = 200.0; A = H / (2 * np.pi)
def g(u):
    t = np.exp(u)
    return t**2 * (2 - t)**3 * np.exp(t - 0.5) if t <= 2 else 0.0
def ghat(xi):
    re = quad(lambda u: g(u) * np.cos(2*np.pi*xi*u), -60, np.log(2), limit=4000)[0]
    im = quad(lambda u: -g(u) * np.sin(2*np.pi*xi*u), -60, np.log(2), limit=4000)[0]
    return re + 1j * im
xs = np.linspace(-A, A, 6001)
gh = np.array([ghat(x) for x in xs])
print("|ghat(+-A)| =", abs(gh[0]), abs(gh[-1]))
for L in [0.0, -2.0, -5.0, -10.0, -20.0, -40.0]:
    val = np.trapezoid(np.exp(2j*np.pi*xs*L) * gh, xs)
    t = np.exp(L); h = t**2*(2-t)**3*np.exp(t-0.5)
    print("t=e^%g: h_H=%.3e  h=%.3e  |h_H-h|/t=%.3e" % (L, val.real, h, abs(val.real - h)/t))
