# The maximum of |eta2DD t| = (2 pi t)^2 |eta2^(t)| on (0, 700], numerically (floating point,
# scipy's sine and cosine integrals). Not used by any proof.
import numpy as np
from scipy.special import sici
from scipy.optimize import minimize_scalar
def J(a, b, x):
    I1 = (sici(b*x)[1] - sici(a*x)[1]) - 1j*(sici(b*x)[0] - sici(a*x)[0])
    return (-np.exp(-1j*b*x)/b + np.exp(-1j*a*x)/a) - 1j*x*I1
def G(x):
    return 16*np.exp(-1j*x/2) - 16*np.exp(-1j*x/4) - 4*np.exp(-1j*x) + 4*J(.25, .5, x) - 4*J(.5, 1, x)
ts = np.linspace(0.01, 700, 700000); v = np.abs(G(2*np.pi*ts)); i = int(np.argmax(v))
r = minimize_scalar(lambda t: -abs(G(2*np.pi*t)), bracket=(ts[i]-0.01, ts[i], ts[i]+0.01))
print("max |eta2DD| ~", -r.fun, "at t ~", r.x)
