"""Generate segment data for the (M) and (m) campaigns.

Outputs tools/segments.json with:
  small_M: list of (L, K, lam, M0, Mend)     per-element Mertens checks, n < 2^18
  large_M: list of (L, K, lam, B, M0, Mend)  band checks, 2^18 <= n <= 1000013823
  ms:      list of (L, K, lam, lo0, hi0, e0, lo1, hi1, e1)  (m)-checks, k <= 602111
M values come from an independent segmented sieve (mu computed by trial-division sieve in C via
mertens_check boundaries) cross-checked here in Python for the small range.
"""
import json, math, subprocess, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from ref import mu_list

HERE = os.path.dirname(os.path.abspath(__file__))
D = 10 ** 20

def segments_small(limit, Kmax=12):
    segs = []
    for e in range(Kmax):           # [2^e, 2^(e+1))
        segs.append((1 << e, e, e))
    L = 1 << Kmax
    while L < limit:
        segs.append((L, Kmax, L.bit_length() - 1)); L += 1 << Kmax
    return segs

def main():
    # --- Mertens values below 2^18 + margin by Python sieve
    NS = 1 << 20
    mu = mu_list(NS)
    M = [0] * (NS + 1)
    for n in range(1, NS + 1): M[n] = M[n - 1] + mu[n]
    small_M = []
    for (L, K, lam) in segments_small(1 << 18):
        S = 1 << K
        small_M.append((L, K, lam, M[L - 1], M[L + S - 1]))
    # --- large segments
    segs = [(j << 18, 18) for j in range(1, 3814)] + [(999817216, 17), (999948288, 16)]
    assert segs[-1][0] + (1 << 16) - 1 == 1000013823
    # M at L-1 for each segment, from the C sieve (prints M(n) for every n = L-1)
    pts = sorted({L - 1 for (L, K) in segs} | {L + (1 << K) - 1 for (L, K) in segs})
    ptsfile = os.path.join(HERE, 'pts.txt')
    open(ptsfile, 'w').write('\n'.join(map(str, pts)) + '\n')
    out = subprocess.run([os.path.join(HERE, 'mertens_at'), ptsfile], capture_output=True, text=True, check=True).stdout
    Mat = dict(tuple(map(int, l.split())) for l in out.split('\n') if l.strip())
    for n in pts:
        if n <= NS: assert Mat[n] == M[n], n
    large_M = []
    for (L, K) in segs:
        lam = L.bit_length() - 1
        B = math.isqrt(326041 * L // 1000000)
        while 1000000 * B * B > 326041 * L: B -= 1
        while 1000000 * (B + 1) ** 2 <= 326041 * L: B += 1
        large_M.append((L, K, lam, B, Mat[L - 1], Mat[L + (1 << K) - 1]))
    # --- (m) segments
    ms = []
    lo = hi = 0; e = 216
    for (L, K, lam) in segments_small(600001):
        S = 1 << K
        st0 = (lo, hi, e)
        for k in range(L, L + S):
            f = mu[k] + 1
            fl, ce = D // k, (D + k - 1) // k
            if f == 2: lo += fl; hi += ce
            elif f == 0: lo -= ce; hi -= fl
            if k >= 11815:
                if (k + 1) ** 16 > 2 ** e: e += 1
                assert (k + 1) ** 16 <= 2 ** e
                A = max(abs(lo), abs(hi))
                assert A * e * 6931471808 <= 48 * D * 10 ** 8, (k, A, e)
        ms.append((L, K, lam, *st0, lo, hi, e))
    json.dump({'small_M': small_M, 'large_M': large_M, 'ms': ms}, open(os.path.join(HERE, 'segments.json'), 'w'))
    print(len(small_M), len(large_M), len(ms))
    print('last large', large_M[-1])
    # margin report for (m)
    worst = 0
    lo = hi = 0; e = 216
    for k in range(1, 600001):
        f = mu[k] + 1
        fl, ce = D // k, (D + k - 1) // k
        if f == 2: lo += fl; hi += ce
        elif f == 0: lo -= ce; hi -= fl
        if k >= 11815:
            if (k + 1) ** 16 > 2 ** e: e += 1
            r = max(abs(lo), abs(hi)) * e * 6931471808 / (48 * D * 10 ** 8)
            if r > worst: worst, wk = r, k
    print('(m) worst ratio to bound', worst, 'at', wk)

if __name__ == '__main__':
    main()
