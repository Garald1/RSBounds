#!/usr/bin/env python3
"""Generator for RSBounds/LambdaCert/{States,Segs/*}.lean and RSBounds/LambdaInputsProof.lean.

This is an exact mirror, in Python integers, of the Nat-only checker in
RSBounds/LambdaCert/Defs.lean (`checkSeg`).  It is *untrusted*: it only produces the literal
intermediate states, which the Lean kernel then re-derives and compares (`decide +kernel`).

Usage (from the project root):  python3 tools/generate.py
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
S = 10**24; S2 = 2 * S; R = 10**15; RR = 10**30; SR = S * R
TOP = 1 << 20
SEG = 4096

def primes_upto(n):
    sv = [True] * (n + 1); sv[0] = sv[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sv[i]:
            for j in range(i * i, n + 1, i): sv[j] = False
    return [i for i in range(n + 1) if sv[i]]

PS = primes_upto(1024)
HP = sorted((p**j, p, j) for p in PS for j in range(2, 21) if p**j <= TOP)

def geom(p, c): return ((1 << (c * p)) - 1) // ((1 << p) - 1)
def firstMult(p, L): return p * max(2, (L + p - 1) // p)
def pat(p, L, B):
    f = firstMult(p, L)
    return (1 << (f - L)) * geom(p, (L + B - f + p - 1) // p) if f < L + B else 0
def compMask(L, B):
    acc = 0
    for p in reversed(PS): acc = pat(p, L, B) | acc
    return acc
def hpMask(L, B):
    acc = 0
    for (q, p, j) in reversed(HP): acc = ((1 << (q - L)) if (L <= q and q < L + B) else 0) | acc
    return acc
def hpLookup(k):
    for (q, p, j) in HP:
        if q == k: return j
    return 0
def serTail(g2, D2, fuel, i, pn, pd):
    if fuel == 0: return (0, (S * pn + pd - 1) // pd)
    if S * pn < pd: return (0, 1)
    t = S2 * pn // ((2 * i + 1) * pd)
    a, b = serTail(g2, D2, fuel - 1, i + 1, pn * g2, pd * D2)
    return (t + a, t + 1 + b)
def logRatio(g, D):
    a, b = serTail(g * g, D * D, 30, 1, g * g * g, D * D * D)
    return (S2 * g // D + a, S2 * g // D + 1 + b)
def newton(N, fuel, x):
    for _ in range(fuel):
        y = (x + N // x) // 2
        if y < x: x = y
        else: return x
    return x
def aBounds(lo, hi):
    if hi <= S: return (True, S - hi, S - lo)
    if S <= lo: return (True, lo - S, hi - S)
    return (False, 0, 0)
def nsub(a, b): return a - b if a >= b else 0

def commonOK(s, t, k, x):
    return (1 <= x and x * x <= k * RR and k * RR <= (x + 1) * (x + 1) and k <= TOP
            and t[4] <= 2 * s[0] * S and t[1] <= k and t[2] <= t[3] and t[5] <= t[6] and t[7] <= t[8])

def stepPP(s, k, x, j):
    n, q, llo, lhi, ahi, glo, ghi, hlo, hhi, sq = s
    d = logRatio(nsub(k, q), k + q)
    l1, l2 = llo + d[0], lhi + d[1]
    ok, al, ah = aBounds(l1 // j, l2 // j + 1)
    t = (k, k, l1, l2, ahi + ah, glo + al // k, ghi + ah // k + 1, hlo + al * R // (x + 1),
         hhi + ah * R // x + 1, x)
    return t if (ok and q < k and 3 * nsub(k, q) <= k + q and commonOK(s, t, k, x)) else None

def stepNP(s, k, x):
    n, q, llo, lhi, ahi, glo, ghi, hlo, hhi, sq = s
    t = (k, q, llo, lhi, ahi + S, glo + S // k, ghi + S // k + 1, hlo + SR // (x + 1),
         hhi + SR // x + 1, x)
    return t if commonOK(s, t, k, x) else None

def advance(s, cb, hb):
    k = s[0] + 1
    x = newton(k * RR, 8, s[9] + RR // (2 * s[9]) + 1)
    if hb == 1:
        j = hpLookup(k)
        return None if j == 0 else stepPP(s, k, x, j)
    return stepPP(s, k, x, 1) if cb == 0 else stepNP(s, k, x)

def runSeg(a, B):
    L = a[0] + 1
    cm, hm, s = compMask(L, B), hpMask(L, B), a
    for _ in range(B):
        s = advance(s, cm % 2, hm % 2)
        if s is None: return None
        cm //= 2; hm //= 2
    return s

INIT = (1, 1, 0, 0, 0, 0, 0, 0, 0, R)
def lean_state(s): return "⟨" + ", ".join(map(str, s)) + "⟩"

HDR = """/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
"""

def main():
    defs = open(os.path.join(ROOT, "RSBounds/LambdaCert/Defs.lean")).read()
    # The tables in Defs.lean must be the ones used here.
    sp = re.search(r"def smallPrimes : List Nat := \[([^\]]*)\]", defs).group(1)
    assert [int(x) for x in sp.split(",")] == PS, "smallPrimes differs"
    hp = re.search(r"def hpList : List \(Nat × Nat × Nat\) := \[(.*?)\]\n", defs).group(1)
    assert [tuple(map(int, t)) for t in re.findall(r"\((\d+), (\d+), (\d+)\)", hp)] == HP, "hpList differs"
    tab = open(os.path.join(ROOT, "RSBounds/LambdaInputs.lean")).read()
    rows = [tuple(map(int, e)) for e in re.findall(r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", tab)]
    assert len(rows) == 45
    bnds = sorted(set(r[0] for r in rows) | set(range(SEG, TOP + 1, SEG)))
    st = [INIT]
    for b in bnds:
        s = runSeg(st[-1], b - st[-1][0])
        if s is None: sys.exit(f"checker fails in the segment ending at {b}")
        st.append(s)
    idx = {s[0]: i for i, s in enumerate(st)}
    E = 10**18
    for (N, gl, gh, hl, hh) in rows:
        s = st[idx[N]]
        if not (gl * E <= s[5] and s[6] <= gh * E and hl * E <= s[7] and s[8] <= hh * E):
            sys.exit(f"row N = {N} is not certified")
    NS = len(st)
    # States.lean
    L = [HDR, "import RSBounds.LambdaCert.Defs\n",
         "/-!\n# The states at the segment boundaries\n\nGenerated by `tools/generate.py`; each consecutive pair is checked in the kernel in\n`RSBounds.LambdaCert.Segs.*`.  The states are at `n = 4096 m` and at the checkpoints of\n`ghTable`.\n-/\n",
         "namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert\n",
         "/-- The initial state. -/\ndef st0 : State := init\n"]
    for i in range(1, NS):
        L.append(f"/-- The state at `n = {st[i][0]}`. -/\ndef st{i} : State := {lean_state(st[i])}\n")
    L.append("end TernaryGoldbach.RSBounds.LambdaInputs.Cert\n")
    open(os.path.join(ROOT, "RSBounds/LambdaCert/States.lean"), "w").write("\n".join(L))
    # Segs/*.lean
    os.makedirs(os.path.join(ROOT, "RSBounds/LambdaCert/Segs"), exist_ok=True)
    segs = list(range(1, NS)); NF = 16; per = (len(segs) + NF - 1) // NF
    files = []
    for f in range(NF):
        part = segs[f * per:(f + 1) * per]
        if not part: continue
        nm = f"Seg{f:02d}"; files.append(nm)
        L = [HDR, "import RSBounds.LambdaCert.States\n",
             f"/-!\n# Kernel checks of segments {part[0]}–{part[-1]} (`n` from {st[part[0]-1][0]} to {st[part[-1]][0]})\n-/\n",
             "namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert\n"]
        for i in part:
            L.append(f"theorem seg{i} : checkSeg st{i-1} st{i} = true := by decide +kernel\n")
        L.append("end TernaryGoldbach.RSBounds.LambdaInputs.Cert\n")
        open(os.path.join(ROOT, f"RSBounds/LambdaCert/Segs/{nm}.lean"), "w").write("\n".join(L))
    # LambdaInputsProof.lean
    L = [HDR, "import RSBounds.LambdaCert.Sound"] + [f"import RSBounds.LambdaCert.Segs.{f}" for f in files]
    L.append(open(os.path.join(ROOT, "tools/proof_head.lean.in")).read())
    for i in range(1, NS):
        L.append(f"theorem inv{i} : Inv st{i} := inv_checkSeg seg{i} inv{i-1}")
    L.append(open(os.path.join(ROOT, "tools/proof_tail.lean.in")).read()
             .replace("@LAST@", str(NS - 1)).replace("@RFLS@", " | ".join(["rfl"] * 45)))
    for (N, gl, gh, hl, hh) in rows:
        L.append(f"  · exact row_of_inv inv{idx[N]} _ rfl (by decide +kernel)")
    L.append("\nend TernaryGoldbach.RSBounds.LambdaInputs\n")
    open(os.path.join(ROOT, "RSBounds/LambdaInputsProof.lean"), "w").write("\n".join(L))
    f = st[-1]
    print(f"{NS} states, {len(files)} segment files; all 45 rows certified")
    print(f"G(2^20) in [{f[5]}, {f[6]}] / 10^24;  H(2^20) in [{f[7]}, {f[8]}] / 10^24")

if __name__ == "__main__":
    main()
