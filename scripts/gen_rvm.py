#!/usr/bin/env python3
"""Generate the RvM certificate data modules and the vendored range statements.

Usage: gen_rvm.py <zeta-zero-locations checkout> <RSBounds project root>

Every certificate is re-checked here in exact rational arithmetic with the same definitions as
`BacklundLowScalar.LogCert` / `RvMFine.FineValid`; Lean re-checks them in the kernel.
"""
import hashlib, re, sys
from fractions import Fraction as Q
from math import floor, ceil

ZZL, PROJ = sys.argv[1], sys.argv[2]
RANGES = [(1000 * j, 1000 * (j + 1)) for j in range(6)]

def name(a, b): return 'Zeros%dto%d' % (a, b)

def read_ords(a, b):
    s = open('%s/challenge/%s.lean' % (ZZL, name(a, b))).read()
    body = s[s.index('def ord0'):s.index('def ordinates')]
    o = [int(x) for x in re.findall(r'\b\d{20,}\b', body)]
    assert o == sorted(o) and len(set(o)) == len(o)
    return s, o

# ---------------------------------------------------------------- vendored statements
def vendor(a, b, src):
    sha = hashlib.sha256(src.encode()).hexdigest()
    n = name(a, b)
    body = src[src.index('namespace %s' % n):]
    # drop the three `sorry` theorems with their docstrings
    cut = body.index('/-- Every zero of')
    end = body.index('end %s' % n)
    body = body[:cut] + body[end:]
    doc = '''import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Vendored statement data of `%s`

Copied from `challenge/%s.lean` of `Garald1/zeta-zero-locations` (commit `371a100`, sha256
`%s`), with two changes only, as in `Zeros0to1000Statement.lean`: the module-system header
(`module`, `public import Mathlib`, `@[expose] public section`) is replaced by
`import Mathlib.NumberTheory.LSeries.RiemannZeta`, and the three theorems `located`, `unique`,
`count`, which that file states with `sorry`, are omitted. The definitions below are unchanged.
`located` and `unique` are restated, as one proposition, in `RvMBound.lean`; nothing in this
project asserts them.
-/

''' % (n, n, sha)
    return doc + body

# ---------------------------------------------------------------- exact checker
def qAux(k, a, b):
    s = 0
    for j in range(k):
        s += 2 * 10**30 * b**(2 * j + 1) // ((2 * j + 1) * (2 * a + b)**(2 * j + 1))
    return s
def qLo(a, b): return qAux(12, a, b)
def qHi(a, b): return qAux(12, a, b) + 12 + 3 * 10**30 * b**25 // (25 * (2 * a + b)**25) + 1
QLO11, QHI11 = qLo(1, 1), qHi(1, 1)
def ratio(c): k, a, b = c; return Q(2)**k * (1 + Q(b, a))
def llower(c): k, a, b = c; return (k * QLO11 + qLo(a, b)) / Q(10**30)
def lupper(c): k, a, b = c; return (k * QHI11 + qHi(a, b)) / Q(10**30)
def lvalid(c): k, a, b = c; return 0 < a and 0 < b and b <= a
P_HI, P_LO = Q(3141593, 500000), Q(3141592, 500000)   # bounds for 2*pi

def fine_valid(t, L, U, lo, hi):
    rl, ru = ratio(L), ratio(U)
    return (lvalid(L) and lvalid(U) and 1 < rl and 0 <= ru and rl * P_HI <= t and t <= ru * P_LO
            and lo < rl * llower(L) - ru + Q(7, 8) and ru * lupper(U) - rl + Q(7, 8) < hi)

A = 10**7
def logcert_below(u):          # 2^k (1 + b/A) <= u, as close as possible
    k = floor(u).bit_length() - 1
    while Q(2)**k > u: k -= 1
    y = u / Q(2)**k
    b = floor((y - 1) * A)
    if b == 0: return (k - 1, A, A)
    return (k, A, b)
def logcert_above(u):          # 2^k (1 + b/A) >= u
    k = floor(u).bit_length() - 1
    while Q(2)**(k + 1) <= u: k += 1
    y = u / Q(2)**k
    b = max(1, ceil((y - 1) * A))
    return (k, A, b)

def cert(t, lo, hi):
    L = logcert_below(t / P_HI)
    U = logcert_above(t / P_LO)
    assert fine_valid(t, L, U, Q(lo), Q(hi)), ('cert fails', float(t), lo, hi)
    return (t, L, U, lo, hi)

def fmt_q(t):
    return str(t.numerator) if t.denominator == 1 else '%d/%d' % (t.numerator, t.denominator)
def fmt(c):
    t, L, U, lo, hi = c
    return '⟨%s, ⟨%d, %d, %d⟩, ⟨%d, %d, %d⟩, %d, %d⟩' % ((fmt_q(t),) + L + U + (lo, hi))

def below_pt(m): return Q(floor(Q(m - 10001, 10**18)), 10**6)
def above_pt(m): return Q(ceil(Q(m + 10001, 10**18)), 10**6)

def chunks(certs, prefix):
    out, names = [], []
    for j in range(0, len(certs), 200):
        nm = '%s%d' % (prefix, j // 200)
        names.append(nm)
        out.append('def %s : List MainCert := [\n  %s]\n' % (nm, ',\n  '.join(fmt(c) for c in certs[j:j + 200])))
    return out, ' ++ '.join(names)

HEADER = '''/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
'''

def facts_text(n, a, b, cnt):
    return '''/-- Length, range and gaps of the listed integers, checked in the kernel. -/
theorem facts : ListFacts %s.ordinates %d %d %d :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
''' % (n, cnt, a, b)

def main():
    data = {}
    for (a, b) in RANGES:
        src, o = read_ords(a, b)
        data[(a, b)] = o
        if a > 0:
            open('%s/RSBounds/%sStatement.lean' % (PROJ, name(a, b)), 'w').write(vendor(a, b, src))
    o0 = data[(0, 1000)]
    # -------- small window [100, 280], c = 1, base 0, global indices 29..125
    K0, K = 29, 126
    assert o0[K0 - 1] + 10001 <= 100 * 10**24 and 280 * 10**24 + 10001 <= o0[K]
    cls = [cert(below_pt(o0[i]), i, i + 2) for i in range(K0, K)]
    chs = [cert(above_pt(o0[i]), i - 1, i + 1) for i in range(K0, K)]
    cA, cB = cert(Q(100), K0 - 1, K0 + 2), cert(Q(280), K - 2, K + 1)
    assert all(c[0] >= 100 for c in cls) and all(c[0] <= 280 for c in chs)
    t1, n1 = chunks(cls, 'lo')
    t2, n2 = chunks(chs, 'hi')
    txt = HEADER + '''import RSBounds.RvMCheck
import RSBounds.Zeros0to1000Statement

/-!
# Certificates for `|N(T) − F(T)| < 1` on `[100, 280]`

For each of the zeros number 30 to 126 (indices 29 to 125), one main-term certificate just below
its bracket and one just above. Generated by `gen_rvm.py`; every check below is kernel arithmetic
on the listed integers and the certificates, and asserts nothing about zeta.
-/

namespace TernaryGoldbach.RSBounds.RvMData0Small
open BacklundLowScalar RvMFine RvMWindow RvMCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0

''' + facts_text('Zeros0to1000', 0, 1000, len(o0)) + '\n' + '\n'.join(t1) + '\n' + '\n'.join(t2) + '''
def cls : List MainCert := %s
def chs : List MainCert := %s
def cA : MainCert := %s
def cB : MainCert := %s

theorem valid : (cls ++ chs ++ [cA, cB]).all (fun x => decide (FineValid x)) = true := by
  decide +kernel

theorem pair : pairCheck 100 280 0 1 29 (Zeros0to1000.ordinates.drop 29) cls chs = true := by
  decide +kernel

theorem below : belowCheck 100 29 Zeros0to1000.ordinates = true := by decide +kernel

theorem above : aboveCheck 280 126 Zeros0to1000.ordinates = true := by decide +kernel

theorem len : cls.length = 126 - 29 := by decide +kernel

theorem ends : cA.t = 100 ∧ ((0 : ℕ) : ℚ) + (29 : ℕ) - (1 : ℕ) ≤ cA.lo ∧
    cB.t = 280 ∧ cB.hi ≤ ((0 : ℕ) : ℚ) + (126 : ℕ) + (1 : ℕ) := by decide +kernel

end TernaryGoldbach.RSBounds.RvMData0Small
''' % (n1, n2, fmt(cA), fmt(cB))
    open('%s/RSBounds/RvMData0Small.lean' % PROJ, 'w').write(txt)
    # -------- c = 3 windows
    wins = [(0, 0, 280, 1000, 126, len(o0), 'Zeros0to1000')]
    base = len(o0)
    for (a, b) in RANGES[1:]:
        o = data[(a, b)]
        wins.append((base, a, a, b, 0, len(o), name(a, b)))
        base += len(o)
    for wi, (base, lo_range, a, b, K0, K, nm) in enumerate(wins):
        o = data[(lo_range, lo_range + 1000)]
        if K0 > 0: assert o[K0 - 1] + 10001 <= a * 10**24
        if K < len(o): assert b * 10**24 + 10001 <= o[K]
        cls = [cert(below_pt(o[i]), base + i - 2, base + i + 2) for i in range(K0, K)]
        cA = cert(Q(a), base + K0 - 3, base + K0 + 3)
        cB = cert(Q(b), base + K - 3, base + K + 2)
        assert all(c[0] >= a for c in cls)
        for i in range(K0, K):     # the next point lies above the bracket of zero i
            nxt = cls[i - K0 + 1][0] if i + 1 < K else cB[0]
            assert o[i] + 10001 <= nxt * 10**24
        t1, n1 = chunks(cls, 'p')
        mod = 'RvMData%d' % wi
        imp = 'RSBounds.%sStatement' % nm
        facts = ('theorem facts : ListFacts Zeros0to1000.ordinates 649 0 1000 := RvMData0Small.facts\n'
                 if wi == 0 else facts_text(nm, lo_range, lo_range + 1000, len(o)))
        txt = HEADER + '''import RSBounds.RvMCheck
import %s%s

/-!
# Certificates for `|N(T) − F(T)| < 3` on `[%d, %d]`

One main-term certificate just below the bracket of each listed zero with index %d to %d, and one
at each end of the window; the certificate of zero `i + 1` (or at `%d`) closes zero `i` from
above. Generated by `gen_rvm.py`; every check below is kernel arithmetic and asserts nothing about
zeta.
-/

namespace TernaryGoldbach.RSBounds.%s
open BacklundLowScalar RvMFine RvMWindow RvMCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0

''' % (imp, '\nimport RSBounds.RvMData0Small' if wi == 0 else '', a, b, K0, K - 1, b, mod) + facts + '\n' + \
            '\n'.join(t1) + '''
def cls : List MainCert := %s
def cA : MainCert := %s
def cB : MainCert := %s

theorem valid : (cls ++ [cA, cB]).all (fun x => decide (FineValid x)) = true := by
  decide +kernel

theorem pair : pairCheck %d %d %d 3 %d (%s.ordinates.drop %d) cls (cls.tail ++ [cB]) = true := by
  decide +kernel

theorem below : belowCheck %d %d %s.ordinates = true := by decide +kernel

theorem above : aboveCheck %d %d %s.ordinates = true := by decide +kernel

theorem len : cls.length = %d - %d := by decide +kernel

theorem ends : cA.t = %d ∧ ((%d : ℕ) : ℚ) + (%d : ℕ) - (3 : ℕ) ≤ cA.lo ∧
    cB.t = %d ∧ cB.hi ≤ ((%d : ℕ) : ℚ) + (%d : ℕ) + (3 : ℕ) := by decide +kernel

end TernaryGoldbach.RSBounds.%s
''' % (n1, fmt(cA), fmt(cB), a, b, base, K0, nm, K0, a, K0, nm, b, K, nm, K, K0,
           a, base, K0, b, base, K, mod)
        open('%s/RSBounds/%s.lean' % (PROJ, mod), 'w').write(txt)
        print(mod, 'window [%d,%d] base %d zeros %d..%d certs %d' % (a, b, base, K0, K - 1, len(cls) + 2))

main()
