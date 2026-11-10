"""Generate a scalar-only certificate for the eight-band budget with the
649-zero head through height 1000 (the 1976 b = 23 row, target 0.00020171).

Same method and machinery as scripts/generate_quartic_budget_certificate.py
(copied below unchanged); only the head changes: height 100 -> 1000, head sum
0.592316 -> 2.028658 (Head1000.weighted_head_le), count 29 -> 649
(Head1000.positiveZeroCount_thousand). delta, the bands, A and every other
term are the same. All enclosures are exact Python fractions and are not
trusted: the generated Lean file checks the expression and logarithm data with
the ordinary kernel and applies QuarticBudgetNumericsBase.Expr.sound.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent.parent
D = 10 ** 30
ARG_SCALE = 10 ** 12
nodes = []
cache = {}


def qtext(q):
    q = Q(q)
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def qbounds(a, b):
    lo = sum(2 * D * b ** (2*j+1) // ((2*j+1) * (2*a+b) ** (2*j+1))
             for j in range(12))
    hi = lo + 12 + 3 * D * b ** 25 // (25 * (2*a+b) ** 25) + 1
    return Q(lo, D), Q(hi, D)


def logcert(q):
    q = Q(q)
    assert q > 1
    k = 0
    while q > 2:
        q /= 2
        k += 1
    a, b = q.denominator, q.numerator-q.denominator
    assert 0 < b <= a
    lo, hi = qbounds(a, b)
    lo2, hi2 = qbounds(1, 1)
    return (k, a, b), k * lo2 + lo, k * hi2 + hi


def make(op, *args):
    key = (op, *args)
    if key in cache:
        return cache[key]
    certs = None
    if op == 'rat':
        lo = hi = Q(args[0])
    elif op == 'pi':
        lo, hi = Q('3.14159265358979323846'), Q('3.14159265358979323847')
    elif op in ('add', 'sub', 'mul'):
        a, b = [nodes[i] for i in args]
        if op == 'add':
            lo, hi = a['lo'] + b['lo'], a['hi'] + b['hi']
        elif op == 'sub':
            lo, hi = a['lo'] - b['hi'], a['hi'] - b['lo']
        else:
            products = [x*y for x in [a['lo'], a['hi']] for y in [b['lo'], b['hi']]]
            lo, hi = min(products), max(products)
    elif op == 'inv':
        a = nodes[args[0]]
        assert a['lo'] > 0
        lo, hi = 1 / a['hi'], 1 / a['lo']
    elif op == 'pow':
        a, n = nodes[args[0]], args[1]
        lo = hi = Q(1)
        for _ in range(n):
            products = [x*y for x in [lo, hi] for y in [a['lo'], a['hi']]]
            lo, hi = min(products), max(products)
    elif op == 'log':
        a = nodes[args[0]]
        low_arg = Q(a['lo'] * ARG_SCALE // 1, ARG_SCALE)
        upper_arg = Q(-((-a['hi'] * ARG_SCALE) // 1), ARG_SCALE)
        cl, lo, _ = logcert(low_arg)
        cu, _, hi = logcert(upper_arg)
        certs = cl, cu
        assert low_arg <= a['lo'] and a['hi'] <= upper_arg
    else:
        raise ValueError(op)
    i = len(nodes)
    nodes.append(dict(op=op, args=args, lo=lo, hi=hi, certs=certs))
    cache[key] = i
    return i


def rat(q): return make('rat', Q(q))
def add(a, b): return make('add', a, b)
def sub(a, b): return make('sub', a, b)
def mul(a, b): return make('mul', a, b)
def div(a, b): return mul(a, make('inv', b))
def power(a, n): return make('pow', a, n)
def log(a): return make('log', a)



delta = Q(211, 10**7)
a = 1 + 2*delta
C = ((1+delta)**5 + 1)**4 / delta**4
A, Y = Q(9472192561, 5000), 2/delta  # A = 1894438.5122
HEAD, S, N0 = 1000, Q(2028658, 10**6), 649
TARGET = Q(20171, 100000000)
L, U = 4/(3*delta), Y-8
cutoffs = [L + (U-L)*j/8 for j in range(9)]
pi = make('pi')
twopi = mul(rat(2), pi)


def F(t):
    z = div(t, twopi)
    return add(mul(z, sub(log(z), rat(1))), rat(Q(7, 8)))


def R(t):
    return add(add(mul(rat(Q(137, 1000)), log(t)),
                   mul(rat(Q(443, 1000)), log(log(t)))), rat(Q(397, 250)))


def J(t):
    first = div(add(div(log(div(t, twopi)), rat(4)), rat(Q(1, 16))),
                mul(twopi, power(t, 4)))
    second = div(rat(Q(137, 1000)), mul(rat(5), power(t, 5)))
    third = div(rat(Q(443, 1000)), mul(mul(rat(5), power(t, 5)), log(t)))
    return add(add(first, second), third)


d, y, h = rat(HEAD), rat(Y), rat(A)
diff_inv = sub(div(rat(1), d), div(rat(1), y))
integral = add(add(div(sub(power(log(div(y, twopi)), 2),
                            power(log(div(d, twopi)), 2)), mul(rat(4), pi)),
                   mul(rat(Q(137, 1000)), diff_inv)),
               div(mul(rat(Q(443, 1000)), diff_inv), log(d)))
W = add(add(mul(rat(a), add(add(rat(S), integral),
                           div(sub(add(F(d), R(d)), rat(N0)), d))),
            mul(rat(C), J(y))),
        mul(mul(rat(2), R(y)), sub(div(rat(C), power(y, 5)), div(rat(a), y))))
K = mul(rat(C), add(J(h), div(mul(rat(2), R(h)), power(h, 5))))
mass = rat(0)
for u, v in zip(cutoffs, cutoffs[1:]):
    u, v = rat(u), rat(v)
    term = div(sub(sub(sub(F(v), R(v)), F(u)), R(u)), v)
    mass = add(mass, term)
coeff = sub(mul(rat(2), W), mul(mul(rat(2), sub(rat(a), rat(Q(931, 1000)))), mass))
budget = add(add(add(mul(rat(2), rat(delta)), K), div(coeff, rat(98715))),
             div(add(add(K, log(twopi)), rat(Q(1, 10))), power(rat(98715), 2)))
assert nodes[coeff]['lo'] > 0
assert nodes[budget]['hi'] < TARGET

header = '''import RSBounds.QuarticFirst29BudgetNumerics

/-!
# Certified scalar budget with the 649-zero head through height 1000

Generated by scripts/generate_quartic_head1000_budget_certificate.py. Only
scalar arithmetic is certified here. The definitions of
`QuarticFirst29BudgetNumerics` (delta, a, C, A, Y, the cutoffs, F, R,
fifthTail, highWeight, bandMass) are reused unchanged; only the line weight
changes, with the head at 1000: head sum 2.028658 and count 649. Every
generated logarithm enclosure and rational comparison is checked by Lean's
ordinary kernel.
-/

namespace TernaryGoldbach.RSBounds.QuarticHead1000BudgetNumerics
open QuarticBudgetNumerics QuarticFirst29BudgetNumerics

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def lowIntegral1000 : ℝ :=
  (Real.log ((Y : ℝ) / (2 * Real.pi)) ^ 2 -
    Real.log ((1000 : ℝ) / (2 * Real.pi)) ^ 2) / (4 * Real.pi) +
    0.137 * (1 / 1000 - 1 / (Y : ℝ)) +
    0.443 * (1 / 1000 - 1 / (Y : ℝ)) / Real.log 1000
noncomputable def lineWeight1000 : ℝ :=
  (a : ℝ) * (2.028658 + lowIntegral1000 + (F 1000 + R 1000 - 649) / 1000) +
    (C : ℝ) * fifthTail (Y : ℝ) +
    2 * R (Y : ℝ) * ((C : ℝ) / (Y : ℝ) ^ 5 - (a : ℝ) / (Y : ℝ))
noncomputable def sqrtCoefficient1000 : ℝ :=
  2 * lineWeight1000 - 2 * ((a : ℝ) - 0.931) * bandMass
noncomputable def scalarBudget1000 : ℝ :=
  2 * (delta : ℝ) + highWeight + sqrtCoefficient1000 / 98715 +
    (highWeight + Real.log (2 * Real.pi) + 0.1) / (98715 : ℝ) ^ 2

/-! The literal expression certificate. LogCert parameters do not enter eval. -/
'''
lines = [header]
def certtext(c): return '⟨' + ', '.join(map(str, c)) + '⟩'
for i, n in enumerate(nodes):
    op, args = n['op'], n['args']
    if op == 'rat': rhs = f'.rat ({qtext(args[0])})'
    elif op == 'pi': rhs = '.pi'
    elif op in ('add', 'sub', 'mul'): rhs = f'.{op} k{args[0]} k{args[1]}'
    elif op == 'inv': rhs = f'.inv k{args[0]}'
    elif op == 'pow': rhs = f'.pow k{args[0]} {args[1]}'
    elif op == 'log': rhs = f'.log {certtext(n["certs"][0])} {certtext(n["certs"][1])} k{args[0]}'
    lines.append(f'private def k{i} : Expr := {rhs}')
all_names = ', '.join(f'k{i}' for i in range(len(nodes)))
public_defs = ('scalarBudget1000, sqrtCoefficient1000, lineWeight1000, lowIntegral1000, '
               'QuarticFirst29BudgetNumerics.bandMass, QuarticFirst29BudgetNumerics.highWeight, '
               'QuarticFirst29BudgetNumerics.fifthTail, QuarticFirst29BudgetNumerics.F, '
               'QuarticFirst29BudgetNumerics.R, QuarticFirst29BudgetNumerics.cutoff, '
               'QuarticFirst29BudgetNumerics.delta, QuarticFirst29BudgetNumerics.a, '
               'QuarticFirst29BudgetNumerics.C, QuarticFirst29BudgetNumerics.A, '
               'QuarticFirst29BudgetNumerics.Y')
lines.append(f'''

def coefficientCertificate1000 : Expr := k{coeff}
def budgetCertificate1000 : Expr := k{budget}

theorem coefficientCertificate1000_checked : coefficientCertificate1000.check = true := by
  decide +kernel

theorem budgetCertificate1000_checked : budgetCertificate1000.check = true := by
  decide +kernel

theorem coefficientCertificate1000_positive : 0 < coefficientCertificate1000.bounds.lo := by
  decide +kernel

theorem budgetCertificate1000_upper :
    budgetCertificate1000.bounds.hi < (20171 / 100000000 : ℚ) := by
  decide +kernel

theorem coefficientCertificate1000_eval : coefficientCertificate1000.eval = sqrtCoefficient1000 := by
  norm_num [coefficientCertificate1000, Expr.eval, {all_names}, {public_defs},
    Finset.sum_range_succ, div_eq_mul_inv]

theorem budgetCertificate1000_eval : budgetCertificate1000.eval = scalarBudget1000 := by
  norm_num [budgetCertificate1000, Expr.eval, {all_names}, {public_defs},
    Finset.sum_range_succ, div_eq_mul_inv]

/-- Positivity needed when replacing sqrt(x) by its lower bound 98715. -/
theorem sqrtCoefficient1000_pos : 0 < sqrtCoefficient1000 := by
  rw [← coefficientCertificate1000_eval]
  exact Expr.eval_pos coefficientCertificate1000_checked coefficientCertificate1000_positive

/-- Only the closed scalar budget is certified; no psi estimate is assumed or concluded. -/
theorem scalarBudget1000_lt : scalarBudget1000 < 0.00020171 := by
  rw [← budgetCertificate1000_eval]
  convert Expr.eval_lt budgetCertificate1000_checked budgetCertificate1000_upper using 1 <;> norm_num

end TernaryGoldbach.RSBounds.QuarticHead1000BudgetNumerics
''')
(ROOT / 'RSBounds/QuarticHead1000BudgetNumerics.lean').write_text('\n'.join(lines))
record = {'status':'generated; Lean kernel verification required', 'nodes':len(nodes),
          'log_nodes':sum(n['op']=='log' for n in nodes),
          'head':HEAD, 'head_sum_bound':qtext(S), 'head_count':N0,
          'sqrt_coefficient_lower':qtext(nodes[coeff]['lo']),
          'sqrt_coefficient_upper':qtext(nodes[coeff]['hi']),
          'budget_lower':qtext(nodes[budget]['lo']), 'budget_upper':qtext(nodes[budget]['hi']),
          'budget_upper_diagnostic':float(nodes[budget]['hi']),
          'target_minus_upper_diagnostic':float(TARGET-nodes[budget]['hi'])}
(ROOT / 'verification/quartic-head1000-scalar-generated.json').write_text(json.dumps(record,indent=2)+'\n')
print({k:v for k,v in record.items() if 'diagnostic' in k or k in ['nodes','log_nodes','status']})
