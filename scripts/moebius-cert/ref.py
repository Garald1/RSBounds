"""Bit-exact Python reference of the kernel checker pipeline (large and small mode).

Validates the sieve/decode logic against a plain mu computation.
"""
import sys, math

def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
    for i in range(2, int(N ** .5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]

PR = primes_upto(31622)
SP = [p for p in PR if p < 1000]
MP = [p for p in PR if p > 1000]
WT = {p: 2 * (p * p).bit_length() - 1 for p in SP}   # 2*log2(p^2)+1  (bit_length-1 = log2)
assert all(WT[p] == 2 * ((p * p).bit_length() - 1) + 1 for p in SP)

def repB(base, d, m):
    return sum(base << (d * j) for j in range(m))

def pat(w, L, S, q, c):
    r = (q - L % q) % q
    if r < S:
        m = (S - 1 - r) // q + 1
        return repB(c << (w * r), w * q, m)
    return 0

def ones(w, n): return repB(1, w, n)

def spread8(X, K):
    """Morton spread: bit i of X (i < 2^K) -> bit 8i."""
    S = 1 << K
    for j in range(K, 0, -1):
        h = 1 << (j - 1)
        LO = repB((1 << h) - 1, 8 * (1 << j), S >> j)
        HI = LO << h
        X = (X & LO) | ((X & HI) << (7 * h))
    return X

def seg_mu1(L, S, lam):
    """returns packed MU1 (8-bit fields, value mu(L+i)+1) for a segment, S = 2^K"""
    K = S.bit_length() - 1; assert 1 << K == S
    th0 = max(0, 5 * lam - 69); th1 = max(0, 5 * lam - 119)
    V = 0
    for p in SP: V += pat(8, L, S, p, WT[p])
    c0 = c1 = 0
    for p in MP:
        P = pat(1, L, S, p, 1)
        c1 |= c0 & P; c0 |= P
    F = 0
    for p in PR: F |= pat(1, L, S, p * p, 1)
    C0, C1, FF = spread8(c0, K), spread8(c1, K), spread8(F, K)
    O = ones(8, S)
    NB0 = ((V + (128 - th0) * O) >> 7) & O
    NB1 = ((V + (128 - th1) * O) >> 7) & O
    PAR = V & O
    NOT = lambda x: x ^ O
    BIG = NOT(C1) & ((NOT(C0) & NOT(NB0)) | (C0 & NOT(NB1)))
    ODD = PAR ^ C0 ^ C1 ^ BIG
    MU1 = FF + ((NOT(FF) & NOT(ODD)) << 1)
    return MU1, V

def mu_list(N):
    mu = [1] * (N + 1); mu[0] = 0
    isp = bytearray([1]) * (N + 1)
    for p in range(2, N + 1):
        if isp[p]:
            for m in range(2 * p, N + 1, p): isp[m] = 0
            for m in range(p, N + 1, p): mu[m] = -mu[m]
            for m in range(p * p, N + 1, p * p): mu[m] = 0
    return mu

def check_large(L, S, lam, B, M0):
    MU1, V = seg_mu1(L, S, lam)
    n4 = S // 4
    O32 = ones(32, n4)
    G = MU1 + (MU1 << 8) + (MU1 << 16) + (MU1 << 24)
    Gr = (G >> 24) & (255 * O32)
    MOD = 1 << (32 * n4)
    def scan(X):
        s = 0
        while (1 << s) < n4:
            X = X + (X << (32 << s)); s += 1
        return X % MOD
    Pf = scan(Gr)
    RAMP = scan(4 * O32)
    H = 1 << 31
    K1 = B - 2 + M0; K2 = B - 2 - M0
    assert K1 >= 0 and K2 >= 0
    E1 = Pf + (H + K1) * O32 - RAMP
    E2 = RAMP + (H + K2) * O32 - Pf
    HM = H * O32
    ok = ((E1 & E2) & HM) == HM
    Plast = Pf >> (32 * (n4 - 1))
    return ok, M0 + Plast - S

if __name__ == "__main__":
    import random
    # validate MU1 decode against true mu on several segments
    N = 1 << 21
    mu = mu_list(N + 10)
    tests = [(1 << 20, 1 << 12, 20), ((1 << 20) + 5 * 4096, 4096, 20), (1 << 16, 1 << 10, 16),
             (2 ** 14, 2 ** 10, 14), (1024, 1024, 10), (16, 16, 4), (2048, 512, 11)]
    for (L, S, lam) in tests:
        MU1, V = seg_mu1(L, S, lam)
        for i in range(S):
            f = (MU1 >> (8 * i)) & 255
            assert f == mu[L + i] + 1, (L, S, i, f, mu[L + i])
        assert MU1 >> (8 * S) == 0
    print("small-range MU1 ok")
    # high range: compare with direct factorization on random samples
    def mu_direct(n):
        r, m = n, 1
        for p in PR:
            if p * p > r: break
            if r % p == 0:
                r //= p
                if r % p == 0: return 0
                m = -m
        if r > 1: m = -m
        return m
    for (L, S, lam) in [(999555072, 4096, 29), (3000 * 262144, 2048, 29), (2 ** 29, 1024, 29), (2 ** 24 + 4096 * 77, 1024, 24),
                        (31907607 - 300, 1024, 24), (1000000000 - 1020, 1024, 29)]:
        MU1, V = seg_mu1(L, S, lam)
        for i in range(S):
            f = (MU1 >> (8 * i)) & 255
            assert f == mu_direct(L + i) + 1, (L, i, f)
    print("high-range MU1 ok")
