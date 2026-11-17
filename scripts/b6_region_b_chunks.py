# Cells per m-chunk of width 1/8 in region B, for each sign s (exact rationals).
import sys
from fractions import Fraction as Fr
src = open('b6_region_b_check.py').read().split('exact = len')[0]
exec(src)
W = Fr(1, 28)
for s in (1, -1):
    out = []
    for i in range(16):
        m0 = Fr(-1) + Fr(i, 8); m1 = m0 + Fr(1, 8)
        cnt[0] = 0
        ok = chkB(60, s, m0, m1, Fr(0), W)
        out.append((float(m0), cnt[0], ok))
    print(s, out)
