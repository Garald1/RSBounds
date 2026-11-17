# Generates RSBounds/HelfgottLow/{Data,States}.lean, Chunk/*.lean, Group/*.lean and AllChunks.lean.
# The Python walk mirrors `step` in RSBounds/HelfgottLow/Defs.lean exactly; its output is candidate
# data only, and every chunk is re-checked by the Lean kernel.
# Run: python3 scripts/gen_helfgott_low.py
import math, os, glob
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'RSBounds', 'HelfgottLow')
SC = 10**15
N0 = 2_000_000
LOG2_UP = 693147180800000   # log 2 < 0.6931471808
LOG2_LO = 693147180300000   # log 2 > 0.6931471803
CH = 10_000
C = [40320, 40320, 20160, 6720, 1680, 336, 56, 8, 1]          # 8!/i!

def trial(n):
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True
D = [m for m in range(5001) if m >= 2 and trial(m)]
P = math.prod(D)
def isSurv(n): return trial(n) if n <= 5000 else math.gcd(n, P) == 1

def expPoly(U): return sum(C[i] * U**i * SC**(8 - i) for i in range(9))
def expcheck(a, b, U):        # log b <= log a + U/SC
    return b * 40320 * SC**8 <= a * expPoly(U)
def expcheckLo(a, b, V):      # log a + V/SC <= log b
    return V <= SC and a * (81 * SC * expPoly(V) + 10 * V**9) <= b * (81 * 40320 * SC**9)
def isqrt_ceil_inv(a):        # least r with SC^2 <= r^2 a
    r = math.isqrt(SC * SC // a)
    while r * r * a < SC * SC: r += 1
    while (r - 1) * (r - 1) * a >= SC * SC: r -= 1
    return r

# ---- anchors (a, l, lo, r) ----
anchors = [(2, LOG2_UP, LOG2_LO, isqrt_ceil_inv(2))]
a, l, lo = 2, LOG2_UP, LOG2_LO
while a <= N0 + 1:
    b = a + 1 if a < 200 else a + a // 200
    U = math.ceil(SC * math.log(b / a))
    while not expcheck(a, b, U): U += 1
    V = math.floor(SC * math.log(b / a))
    while not expcheckLo(a, b, V): V -= 1
    a, l, lo = b, l + U, lo + V
    anchors.append((a, l, lo, isqrt_ceil_inv(a)))
# sanity: the bounds are bounds
for (a, l, lo, r) in anchors[::50]:
    assert lo / SC <= math.log(a) + 1e-12 and math.log(a) <= l / SC + 1e-12

events = sorted((m**k, k) for m in D for k in range(2, 25) if m**k <= 25_000_000)  # HelfgottSmall.eventsAll
def eOf(i): return events[i] if i < len(events) else (0, 0)
DF = (0, 0, 0, 0)
def headD(L, i): return L[i] if i < len(L) else DF   # head of anchors[i:]

RHO0 = math.isqrt(SC * SC // (N0 + 1))
assert RHO0 * RHO0 * (N0 + 1) <= SC * SC

def weight(n, a, l): return l + ((n - a) * SC + (a - 1)) // a
def lowW(n, a, lo): return lo + ((n - a) * SC) // n
def incR(n, a, r, inc):
    den = 2 * n * SC
    return (inc * r * (a + n) + den - 1) // den

# state: n psi s t d ia a l lo r b ja aL loL bL ie q k   (ra = anchors[ia+1:], rl = anchors[ja+1:])
def step(st):
    n, psi, s, t, d, ia, a, l, lo, r, b, ja, aL, loL, bL, ie, q, k = st
    if n == b:
        if ia + 1 >= len(anchors): return None
        ia += 1; a, l, lo, r = anchors[ia]; b = headD(anchors, ia + 1)[0]
    if not (a <= n and 2 <= a and n <= N0): return None
    surv = isSurv(n)
    if surv or q == n:
        w = weight(n, a, l)
    inc = 0; add = 0
    if surv:
        inc = w; add = w * w
    if q == n:
        inc += (w + k - 1) // k
        ie += 1; q, k = eOf(ie)
    psi += inc; s += n * inc
    if inc != 0: t += incR(n, a, r, inc)
    d += add
    if n % 2 == 0 and n >= 4:
        m = n // 2
        if m == bL:
            if ja + 1 >= len(anchors): return None
            ja += 1; aL, _, loL, _ = anchors[ja]; bL = headD(anchors, ja + 1)[0]
        if not (aL <= m and 2 <= aL): return None
        if isSurv(m):
            v = lowW(m, aL, loL)
            d = max(0, d - v * v)
    if 663 <= n <= 1_600_000 and not (200000 * s < 103884 * n * n * SC): return ('fail16', n)
    if not (100000000 * t * t < 400320064 * n * SC * SC): return ('fail18', n)
    if n >= 117 and not (2 * d <= n * lowW(n, a, lo) * SC): return ('fail19', n)
    return (n + 1, psi, s, t, d, ia, a, l, lo, r, b, ja, aL, loL, bL, ie, q, k)

a0 = anchors[0]
st = (2, 0, 0, 0, 0, 0, a0[0], a0[1], a0[2], a0[3], anchors[1][0], 0, a0[0], a0[2], anchors[1][0],
      0, events[0][0], events[0][1])
states = [st]; fuels = []
# float margins along the way
worst = {}
while st[0] <= N0:
    f = min(CH, N0 + 1 - st[0])
    for _ in range(f):
        st2 = step(st)
        assert st2 is not None and len(st2) == 18, ("check failed", st2, st[0])
        st = st2
    states.append(st); fuels.append(f)
n, psi, s, t, d = st[:5]
lhs = SC * t - RHO0 * psi
finalB = 100000000 * max(lhs, 0) ** 2 < 100080016 * N0 * SC**4
print("anchors", len(anchors), "events<=N0", sum(1 for e in events if e[0] <= N0), "chunks", len(fuels),
      "final n", n, "finalB", finalB, "B slack", 1.0004 * math.sqrt(N0) - lhs / SC**2)
assert finalB

if __name__ == "__main__" and os.environ.get("WRITE", "1") == "1":
    os.makedirs(OUT, exist_ok=True)
    def chunks(lst, size): return [lst[i:i + size] for i in range(0, len(lst), size)]
    def fmt4(lst, per_line=2):
        items = [f"({x}, {y}, {z}, {w})" for x, y, z, w in lst]
        lines = [", ".join(items[i:i + per_line]) for i in range(0, len(items), per_line)]
        return "[" + ",\n  ".join(lines) + "]"
    with open(f"{OUT}/Data.lean", "w") as f:
        f.write("/-!\n# Anchors for the walk of `HelfgottLow`\n\nGenerated by `scripts/gen_helfgott_low.py`. "
                "Nothing here is trusted: `DataChecks.lean` checks every property that is used.\n-/\n\n"
                "namespace RSBounds.HelfgottLow\n\n")
        names = []
        for i, ch in enumerate(chunks(anchors, 250)):
            nm = f"anchors{i}"; names.append(nm)
            f.write(f"/-- Anchors `(a, l, lo, r)`, part {i}. -/\ndef {nm} : List (Nat × Nat × Nat × Nat) :=\n  "
                    + fmt4(ch) + "\n\n")
        f.write("/-- All anchors: `log a ≤ l / 10¹⁵`, `lo / 10¹⁵ ≤ log a`, `10³⁰ ≤ r² a`. -/\n"
                "def anchorsAll : List (Nat × Nat × Nat × Nat) :=\n  " + " ++ ".join(names) +
                "\n\nend RSBounds.HelfgottLow\n")
    NCH = len(fuels); PER = 50
    def ext(t):  # boundary data: n psi s t d ia ja ie
        return (t[0], t[1], t[2], t[3], t[4], t[5], t[11], t[15])
    def tup(t): return "(" + ", ".join(str(x) for x in t) + ")"
    with open(f"{OUT}/States.lean", "w") as f:
        f.write("import RSBounds.HelfgottLow.Defs\n\n/-!\n# Chunk boundaries of the walk\n\n"
                "Generated by `scripts/gen_helfgott_low.py`. Each chunk theorem checks that the walk goes "
                "from `attach (extOf i)` to `attach (extOf (i + 1))` in `fuelOf i` steps.\n-/\n\n"
                "namespace RSBounds.HelfgottLow\n\n")
        names = []
        for i, ch in enumerate(chunks([ext(t) for t in states], 100)):
            nm = f"exts{i}"; names.append(nm)
            f.write(f"set_option maxRecDepth 8000 in\n/-- Chunk boundaries, part {i}. -/\ndef {nm} : List Ext :=\n  [" +
                    ",\n   ".join(tup(t) for t in ch) + "]\n\n")
        f.write("/-- All chunk boundaries. -/\ndef extsAll : List Ext :=\n  " + " ++ ".join(names) + "\n\n")
        f.write("/-- The boundary data at the start of chunk `i`. -/\ndef extOf (i : Nat) : Ext :=\n"
                "  extsAll.getD i (0, 0, 0, 0, 0, 0, 0, 0)\n\n")
        f.write(f"/-- The number of steps in chunk `i`. -/\ndef fuelOf (i : Nat) : Nat :=\n"
                f"  if i = {NCH - 1} then {fuels[-1]} else {fuels[0]}\n\n")
        f.write("/-- Chunk `i` checks out. -/\nabbrev ChunkGood (i : Nat) : Prop :=\n"
                "  chunkOK (fuelOf i) (extOf i) (extOf (i + 1)) = true\n\n"
                f"/-- The number of chunks. -/\ndef NCH : Nat := {NCH}\n\nend RSBounds.HelfgottLow\n")
    assert all(x == fuels[0] for x in fuels[:-1])
    ngroups = (NCH + PER - 1) // PER
    for old in glob.glob(f"{OUT}/Chunk/*.lean") + glob.glob(f"{OUT}/Group/*.lean"): os.remove(old)
    os.makedirs(f"{OUT}/Chunk", exist_ok=True); os.makedirs(f"{OUT}/Group", exist_ok=True)
    for i in range(NCH):
        with open(f"{OUT}/Chunk/C{i:04d}.lean", "w") as f:
            f.write("import RSBounds.HelfgottLow.States\n\n"
                    f"/-! Walk chunk {i}, checked by the kernel (one chunk per module, to bound memory). -/\n\n"
                    f"theorem RSBounds.HelfgottLow.chunk_{i} : RSBounds.HelfgottLow.ChunkGood {i} := by\n"
                    "  decide +kernel\n")
    for g in range(ngroups):
        lo_, hi = g * PER, min(NCH, (g + 1) * PER)
        with open(f"{OUT}/Group/G{g:02d}.lean", "w") as f:
            for i in range(lo_, hi):
                f.write(f"import RSBounds.HelfgottLow.Chunk.C{i:04d}\n")
            f.write(f"\n/-! Walk chunks {lo_} to {hi - 1}. -/\n\nnamespace RSBounds.HelfgottLow\n\n")
            f.write(f"theorem group_{g} (t : Nat) (ht : t < {hi - lo_}) : ChunkGood ({lo_} + t) :=\n"
                    "  match t, ht with\n")
            for i in range(lo_, hi):
                f.write(f"  | {i - lo_}, _ => chunk_{i}\n")
            f.write(f"  | _ + {hi - lo_}, h => absurd h (by omega)\n\nend RSBounds.HelfgottLow\n")
    with open(f"{OUT}/AllChunks.lean", "w") as f:
        for g in range(ngroups):
            f.write(f"import RSBounds.HelfgottLow.Group.G{g:02d}\n")
        f.write("\n/-!\n# All chunks of the walk\n-/\n\nnamespace RSBounds.HelfgottLow\n\n"
                f"theorem chunkGood_all (i : Nat) (hi : i < NCH) : ChunkGood i := by\n"
                f"  have hi' : i < {NCH} := hi\n")
        for g in range(ngroups):
            lo_, hi = g * PER, min(NCH, (g + 1) * PER)
            f.write(f"  if h{g} : i < {hi} then\n    have e : i = {lo_} + (i - {lo_}) := by omega\n"
                    f"    exact e ▸ group_{g} (i - {lo_}) (by omega)\n  else\n")
        f.write("  exact absurd hi' (by omega)\n\nend RSBounds.HelfgottLow\n")
    print("wrote", NCH, "chunks in", ngroups, "groups; RHO0 =", RHO0)
