"""Exact-rational interval audit of the RS75 residual (not a Lean proof).

Square-root boxes are checked by squaring integer/rational endpoints. Log
boxes use the positive artanh series with an explicit geometric remainder.
The Euler-constant box is the already checked SmallTotientProduct.gamma_bounds;
the pi box is Mathlib's pi_gt_d20/pi_lt_d20. No floating-point values enter
the assertions. The output is evidence for a subsequent Lean scalar proof.
"""
from dataclasses import dataclass
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import hashlib
import json


@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def point(x):
        return I(Q(x), Q(x))

    def __add__(self, other):
        other = box(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -box(other)

    def __rsub__(self, other):
        return box(other) + -self

    def __mul__(self, other):
        other = box(other)
        ends = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(ends), max(ends))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = box(other)
        assert other.lo > 0 or other.hi < 0
        return self * I(1 / other.hi, 1 / other.lo)

    def __rtruediv__(self, other):
        return box(other) / self

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        r = box(1)
        for _ in range(n):
            r = r * self
        return r


def box(x):
    return x if isinstance(x, I) else I.point(x)


def sqrt_box(x):
    x = Q(x)
    assert x > 0
    scale = 10**60
    n = isqrt(x.numerator * scale**2 // x.denominator)
    lo, hi = Q(n, scale), Q(n + 1, scale)
    assert lo * lo <= x <= hi * hi
    return I(lo, hi)


def log_small(x):
    """Enclose log(x), 1 <= x <= 2, by 80 exact artanh terms."""
    x = Q(x)
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    n = 80
    partial = 2 * sum((z ** (2*j + 1) / (2*j + 1) for j in range(n)), Q(0))
    tail = 2 * z**(2*n + 1) / ((2*n + 1) * (1 - z*z))
    return I(partial, partial + tail)


def log_box(x):
    x = Q(x)
    assert x > 0
    if x < 1:
        return -log_box(1/x)
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    return log_small(x) + k * log_small(2)


def log_interval(x):
    return I(log_box(x.lo).lo, log_box(x.hi).hi)


def poly_add(a, b):
    return [(a[i] if i < len(a) else Q(0)) +
            (b[i] if i < len(b) else Q(0)) for i in range(max(len(a), len(b)))]


def poly_mul(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def dec(q, rounding):
    with localcontext() as c:
        c.prec = 42
        c.rounding = rounding
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def encode(x):
    x = box(x)
    return {"lower": str(x.lo), "upper": str(x.hi),
            "decimal_lower": dec(x.lo, ROUND_FLOOR),
            "decimal_upper": dec(x.hi, ROUND_CEILING)}


a = list(map(Q, ['11.1859355312082048', '19.073344004352',
                '11.67618784', '4.7568', '1']))
A0 = sum(a[1:])
assert A0 == Q('36.506331844352')
D0, A, h, h30 = Q('52.38865'), Q(1894439), Q('.029172'), Q('.03')
gamma = I(Q('.5772156646'), Q('.577215666'))
pi = I(Q('3.14159265358979323846'), Q('3.14159265358979323847'))
D = sum((a[k] * log_interval(2*pi/k) for k in range(1, 5)), box(0))
sum_weighted = sum(a[k]/k**2 for k in range(1, 5))
assert D.lo > D0 and sum_weighted < Q('22.584')
E = 17 * Q('22.584') / (3*A*A)
b = 1/sqrt_box(5)
C = (1-b)*A0/2
v = sqrt_box(a[0]) * (sqrt_box(a[1])-sqrt_box(a[0])) / C
R1 = C / (sqrt_box(a[1])-sqrt_box(a[0]))**2
log17 = log_box(17)
x_at_A = v / log_box(A/17)
assert x_at_A.hi < h
assert R1.hi < Q('9.645908801')
assert log_box(A).lo > 14

# Improved kappa lower bound: b*(1 + .8*x - 1.04*x^2 + 1.2*x^3).
P = list(map(Q, ['1', '.8', '-1.04', '1.2']))
square_gap = poly_add([Q(5), Q(20), Q(20)],
                     [-q for q in poly_mul([Q(5), Q(12), Q(8)], poly_mul(P, P))])
expected_gap = [Q(0)]*3 + [4*Q(q)/625 for q in
                          [125, -1925, -4598, -197, 420, -1800]]
assert square_gap == expected_gap
gap_bracket_lower = (Q(125) - 1925*h30 - 4598*h30**2
                     - 197*h30**3 - 1800*h30**5)
assert gap_bracket_lower > 63
assert 1 - Q('1.04')*h30*h30 > 0

# The coefficient of kappa in Lemma 2 is negative throughout the needed range.
q0, q1, near = Q('-1.1398'), Q('3.3606'), Q('.2')
assert q0 + q1*h30 < 0
assert -7*A0 + D0/2 < 0

# Upper bound for the full residual plus C*log(17), after replacing kappa by b*P.
k = [b*p for p in P]
coeff = [
    -k[1]*A0*v/2 + a[0]*(k[0]*q0-gamma) - (1-k[0])*D0/2 + E + C*log17,
    -k[2]*A0*v/2 - k[1]*A0*log17/2 + a[0]*(k[1]*q0+k[0]*q1) + k[1]*D0/2 + near*a[0],
    -k[3]*A0*v/2 - k[2]*A0*log17/2 + a[0]*(k[2]*q0+k[1]*q1) + k[2]*D0/2,
    -k[3]*A0*log17/2 + a[0]*(k[3]*q0+k[2]*q1) + k[3]*D0/2,
    a[0]*k[3]*q1,
]
rounded_upper = list(map(Q, ['-.2649148', '8.23461', '27.92797', '-38.02198', '20.1737']))
assert all(c.hi < r for c, r in zip(coeff, rounded_upper))
assert coeff[1].lo > 0 and coeff[2].lo > 0 and coeff[3].hi < 0 and coeff[4].lo > 0
deriv_lower = coeff[1].lo + 3*coeff[3].lo*h*h
assert deriv_lower > Q('8.13')
endpoint = sum((c*h**j for j, c in enumerate(coeff)), box(0))
assert endpoint.hi < Q('-.0018574')
simple_upper = sum(rounded_upper[j]*h**j for j in [0, 1, 2, 4])
assert simple_upper < Q('-.0009')

# Compare against the rounded cubic printed on p. 250.
paper_p = Q('-28.85290') + Q('8.0365')*h + Q('31.574')*h*h - Q('17.76')*h**3
paper_margin = -C*log17 - paper_p
near_cost = a[0]*(near-Q('.1876352'))*h
gold_cost_cap = a[0]*Q('.458')*(Q('.0001158')+Q('.02567')*h)
kappa_endpoint = (1+2*h)/sqrt_box(5+12*h+8*h*h)
gold_cost_at_endpoint = a[0]*kappa_endpoint*(Q('.0001158')+Q('.02567')*h)
assert (paper_margin-near_cost).lo > 0
assert (paper_margin-near_cost-gold_cost_at_endpoint).hi < 0

script = Path(__file__)
out = {
    "status": "exact-rational-interval-audit-passed-not-Lean",
    "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
    "inputs": {"gamma_box_source": "SmallTotientProduct.gamma_bounds (checked)",
               "pi_box_source": "Mathlib Real.pi_gt_d20 / Real.pi_lt_d20",
               "log_method": "80-term artanh series; explicit geometric remainder",
               "sqrt_method": "60-decimal rational endpoints verified by squaring",
               "A": str(A), "x_upper": str(h),
               "near_pole_slope": str(near), "golden_intercept": str(q0), "golden_slope": str(q1)},
    "derived": {"D": encode(D), "C": encode(C), "v": encode(v), "R1": encode(R1),
                "x_at_A": encode(x_at_A), "E_cap": encode(E),
                "kappa_square_gap_bracket_lower": encode(gap_bracket_lower),
                "paper_margin": encode(paper_margin), "near_pole_cost": encode(near_cost),
                "golden_cost_cap": encode(gold_cost_cap),
                "paper_margin_after_near": encode(paper_margin-near_cost),
                "paper_margin_after_both_endpoint_costs": encode(paper_margin-near_cost-gold_cost_at_endpoint),
                "paper_margin_after_both_capped_costs": encode(paper_margin-near_cost-gold_cost_cap),
                "new_residual_coefficients": [encode(c) for c in coeff],
                "new_residual_rounded_upper_coefficients": list(map(str, rounded_upper)),
                "new_residual_derivative_lower": encode(deriv_lower),
                "new_residual_at_endpoint": encode(endpoint),
                "new_residual_simple_global_upper": encode(simple_upper)},
}
target = script.with_suffix('.json')
target.write_text(json.dumps(out, indent=2)+'\n')
print(out['status'])
for name in ['R1', 'x_at_A', 'paper_margin_after_near',
             'paper_margin_after_both_capped_costs', 'new_residual_at_endpoint',
             'new_residual_simple_global_upper']:
    z = out['derived'][name]
    print(name, '[', z['decimal_lower'], ',', z['decimal_upper'], ']')
