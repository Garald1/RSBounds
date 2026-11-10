"""Generate the kernel-checked theta/psi walk certificates for the finite parts of
Schoenfeld (1976), Theorem 7*: (5.5a*), (5.5b*), (5.6a*), (5.6*).

The walk (RSBounds/SchoenfeldPrimeWalk.lean) is replicated here exactly, in integer arithmetic,
so that every intermediate state can be written into the Lean files; Lean recomputes each segment
with `decide +kernel`, so nothing computed here is trusted.

Segments and thresholds (all scaled by D = 10^30). For x in [n, n+1):
  * (5.6a*), n < N56A:          theta(x) - x < 0                         (thUp = 0)
  * psi(y) <= 1.04 y, n < NPS:  psi(x) - x < 0.04 A                      (psUp)
  * (5.5b*), N55B <= n < N55E:  x - psi(x) < c55 A / log A               (psLo)
  * (5.5a*), N55A <= n < N55E:  psi(x) - x < c55 A / log A               (psUp)
  * (5.6*),  N56 <= n < N56E:   |theta(x) - x| < c56 A / log A           (thUp, thLo)
where A is the start of the segment; A/log A <= x/log x for x >= A >= e. Lean checks that each
threshold is at most D c A / log A using an upper bound for D log A (`thresholdOk`).
Usage: python3 -I scripts/generate_schoenfeld_prime_walk.py [--emit] [--test FILE]
"""
import sys
from pathlib import Path
from fractions import Fraction as F

ROOT = Path(__file__).resolve().parent.parent
D = 10 ** 30
HUGE = 10 ** 80

N56A = 250000          # (5.6a*): theta(x) < x below this; PsiCert above 242804
NPS = 100000           # psi(y) <= 1.04 y below this
N55B, N55A, N55E = 89909, 161971, 200000   # (5.5b*), (5.5a*); PsiCert above 195071
N56, N56E = 758711, 1350000                # (5.6*); PsiCert + psi - theta above ~1317859
C55 = F(220646, 10 ** 7)
C56 = F(239922, 10 ** 7)
NEND = N56E


def qAux(k, a, b):
    s = 0
    for j in range(k):
        s += 2 * D * b ** (2 * j + 1) // ((2 * j + 1) * (2 * a + b) ** (2 * j + 1))
    return s


def qLo(a, b): return qAux(12, a, b)
def qHi(a, b): return qAux(12, a, b) + 12 + 3 * D * b ** 25 // (25 * (2 * a + b) ** 25) + 1


Q11LO, Q11HI = qLo(1, 1), qHi(1, 1)


def lg(m):
    k, a = 0, 1
    for _ in range(64):
        if 2 * a <= m - 1:
            k, a = k + 1, 2 * a
        else:
            break
    return k, a


def logLo(m):
    k, a = lg(m)
    return k * Q11LO + qLo(a, m - a)


def logHi(m):
    k, a = lg(m)
    return k * Q11HI + qHi(a, m - a)


def sieve(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def run():
    spf = sieve(NEND + 2)
    # states[n] = (Tlo, Thi, Plo, Phi) for theta(n), psi(n)
    T = [None] * (NEND + 2)
    s = (0, 0, 0, 0)
    T[1] = s
    logc = {}
    for m in range(2, NEND + 2):
        p = spf[m]
        if p == m:
            lo, hi = logc.setdefault(m, (logLo(m), logHi(m)))
            s = (s[0] + lo, s[1] + hi, s[2] + lo, s[3] + hi)
        else:
            q = m
            while q % p == 0:
                q //= p
            if q == 1:
                lo, hi = logc.setdefault(p, (logLo(p), logHi(p)))
                s = (s[0], s[1], s[2] + lo, s[3] + hi)
        T[m] = s
    return T


def threshold(c, A):
    """floor(D c A / (logHi(A)/D)), a lower bound for D c A / log A."""
    return (c.numerator * A * D * D) // (c.denominator * logHi(A))


def need(n, st):
    """The four exact requirements at n (minimal thresholds that pass), scaled by D."""
    Tlo, Thi, Plo, Phi = st
    return (Thi - D * n + 1, D * (n + 1) - Tlo, Phi - D * n + 1, D * (n + 1) - Plo)


def active(n):
    return dict(thUp0=n < N56A, psU=n < NPS, psLo55=N55B <= n < N55E, psUp55=N55A <= n < N55E,
                th56=N56 <= n < N56E)


def req_for(A):
    a = active(A)
    thUp = 0 if a['thUp0'] else (threshold(C56, A) if a['th56'] else HUGE)
    thLo = threshold(C56, A) if a['th56'] else HUGE
    psUp = HUGE
    if a['psU']:
        psUp = D * A * 4 // 100
    if a['psUp55']:
        psUp = min(psUp, threshold(C55, A))
    psLo = threshold(C55, A) if a['psLo55'] else HUGE
    return (thUp, thLo, psUp, psLo)


BOUNDARIES = sorted({1, N55B, N55A, NPS, N55E, N56A, N56, N56E})


def plan(T, maxlen=5000):
    """Segments [A, B) inside the regions between boundaries; each checks every n with req_for(A)."""
    segs = []
    for lo, hi in zip(BOUNDARIES, BOUNDARIES[1:]):
        A = lo
        while A < hi:
            r = req_for(A)
            B = A
            while B < hi and B - A < maxlen:
                nd = need(B, T[B])
                if not (nd[0] <= r[0] and nd[1] <= r[1] and nd[2] <= r[2] and nd[3] <= r[3]):
                    break
                B += 1
            if B == A:
                raise SystemExit(f"stuck at {A}: need {need(A, T[A])} req {r}")
            segs.append((A, B - A, r))
            A = B
    return segs


def main():
    T = run()
    segs = plan(T)
    print("segments", len(segs), "end", segs[-1][0] + segs[-1][1])
    for n in [N55B, N55A, N55E, N56A, N56, N56E]:
        print(n, "theta", T[n][0] / D, "psi", T[n][2] / D)
    if '--emit' in sys.argv:
        emit(T, segs)
    if '--test' in sys.argv:
        test(T, segs)


def lit(st): return '⟨' + ', '.join(map(str, st)) + '⟩'


HEADER = ""


def seg_text(T, A, L, r):
    return (f"theorem seg_{A} : Seg {A} {A + L} {lit(T[A])} {lit(T[A + L])} :=\n"
            f"  seg_of (L := {L}) ⟨{r[0]}, {r[1]}, {r[2]}, {r[3]}⟩ (by norm_num) (by norm_num)\n"
            f"    (by decide +kernel)\n")


def chain(names):
    return names[0] if len(names) == 1 else f"{names[0]}.trans ({chain(names[1:])})"


def emit(T, segs, per_file=16):
    chunks = [segs[i:i + per_file] for i in range(0, len(segs), per_file)]
    mods = []
    for ci, chunk in enumerate(chunks):
        name = f"SchoenfeldPrimeWalkData{ci:02d}"
        mods.append(name)
        A0, B = chunk[0][0], chunk[-1][0] + chunk[-1][1]
        out = [HEADER + "import RSBounds.SchoenfeldPrimeWalk\n",
               f"/-! Generated by `scripts/generate_schoenfeld_prime_walk.py`: the walk on "
               f"`[{A0}, {B})`, every segment recomputed by the kernel. -/\n",
               "namespace TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk\n",
               "set_option maxRecDepth 100000\n"]
        for (A, L, r) in chunk:
            out.append(seg_text(T, A, L, r))
        out.append(f"theorem part_{ci:02d} : Seg {A0} {B} {lit(T[A0])} {lit(T[B])} :=\n  "
                   + chain([f"seg_{A}" for (A, _, _) in chunk]) + "\n")
        out.append("end TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk\n")
        (ROOT / f"RSBounds/{name}.lean").write_text('\n'.join(out))
    out = [HEADER] + [f"import RSBounds.{m}" for m in mods] + [
        "",
        "/-! Generated by `scripts/generate_schoenfeld_prime_walk.py`: the whole walk. -/",
        "",
        "namespace TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk",
        "",
        f"theorem walk_all : Seg 1 {NEND} {lit(T[1])} {lit(T[NEND])} :=",
        "  " + chain([f"part_{ci:02d}" for ci in range(len(chunks))]),
        "",
        f"theorem good {{n : ℕ}} (h1 : 1 ≤ n) (h2 : n < {NEND}) : Good n :=",
        "  (walk_all Inv_one).2 n h1 h2",
        "",
        "end TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk",
        ""]
    (ROOT / "RSBounds/SchoenfeldPrimeWalkAll.lean").write_text('\n'.join(out))
    print("wrote", len(mods), "data modules")


def test(T, segs):
    """One full-length segment near the top, for timing."""
    A, L, r = [sg for sg in segs if sg[1] == 5000][-1]
    out = ["import RSBounds.SchoenfeldPrimeWalk",
           "namespace TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk",
           "set_option maxRecDepth 100000", seg_text(T, A, L, r),
           "end TernaryGoldbach.RSBounds.SchoenfeldPrimeWalk"]
    Path(sys.argv[sys.argv.index('--test') + 1]).write_text('\n'.join(out) + '\n')
    print("test segment", A, L)


if __name__ == '__main__':
    main()
