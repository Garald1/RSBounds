# Kernel-checked von Mangoldt computations (L)

Proofs of the two statements of `RSBounds/LambdaInputs.lean` (unchanged; sha256
`f26c9834705f783d6be278d7b8ab9ce19ae5c386d576a6aaefca6747ae5e5da0`):

```lean
theorem TernaryGoldbach.RSBounds.LambdaInputs.weightSumBound : WeightSumBound
theorem TernaryGoldbach.RSBounds.LambdaInputs.ghBounds : GHBounds
```

both in `RSBounds/LambdaInputsProof.lean`.

Pins: Lean `leanprover/lean4:v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`
(standalone Lake project depending only on Mathlib).

```
lake exe cache get
lake build
```

## Results

* `#print axioms` (both theorems): `[propext, Classical.choice, Quot.sound]`.
  No `native_decide`, no `sorry`, no new axioms. See `logs/axioms.txt`.
* Build: 24 project modules; 178 s wall time on a 2-core x86_64 Linux machine (Mathlib from
  the cache, project modules built from scratch). The 16 kernel-check modules take 2.5–23 s
  each. See `logs/build.log`.
* `lake comparator` (the successor of leanprover/comparator, built into Lean 4.35.0), sandboxed with
  `bwrap` (bubblewrap 0.9.0), with challenge `LambdaChallenge.lean` (imports the unchanged
  statement file and states both theorems with `sorry`) and solution `RSBounds.LambdaInputsProof`:
  "Lean default kernel accepts the solution / Your solution is okay!" (424 s).
  Config: `comparator.json`. Log: `logs/comparator.log`.
* The same with `--paranoid`, which also runs the external checkers bundled with Lean 4.35.0:
  `leanchecker-paranoid`, `lean4lean` (28354 declarations), `nanoda`, `con-leche` and `con-ron`
  (28357 declarations each). All accept (2421 s). Log: `logs/comparator-paranoid.log`.
* All 45 rows of `ghTable` are proved as given; no row needed widening.
* Certified enclosures at `N = 2^20` (scale `10^24`):
  `G ∈ [20.011881183058320409107379, 20.011881183058320410183962]`,
  `H ∈ [3723.992675668264486436143809, 3723.992675668264506465851768]`,
  consistent with the note's `G(2^20) = 20.011881`, `H(2^20) = 3723.99268`.

## Method

One pass over `k = 2, …, 2^20`, cut into 292 segments whose ends are `n = 4096 m` and the 45
checkpoints of `ghTable`. The state after processing `2, …, n` (`Cert.State`) holds, in fixed
point with scale `S = 10^24`:

* `q`, the last prime power `≤ n` (or `1`), and lower/upper bounds for `S log q`;
* an upper bound for `S·A(n)`;
* lower and upper bounds for `S·G(n)` and `S·H(n)`;
* `sq = ⌊√(n·10^30)⌋`.

**Classification of `k`.** For each segment `[L, L+B)` the checker builds two bit masks with
big-`Nat` operations: the sieve mask, with bit `m − L` set for every multiple `m ≥ 2p` of each prime
`p ≤ 1024` (each prime's pattern is `2^o · (2^{cp} − 1)/(2^p − 1)`), and the mask of the 242 prime
powers `p^j ≤ 2^20` with `j ≥ 2` (`hpList`). An unset sieve bit means `k` is prime; a set sieve bit
with an unset `hpList` bit means `k` is not a prime power; for `k` in `hpList` the exponent `j` is
read from the list.

**Logarithms.** Only at prime powers: `log k = log q + log((1+x)/(1−x))` with `x = (k−q)/(k+q)`,
using Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one` (the `artanh` series). Terms are rounded
down for the lower bound and up for the upper bound. The series is truncated once
`S·g^{2i+1} < D^{2i+1}`, and the tail from `i ≥ 1` is bounded by `x^{2i+1}`, which holds since the
checker verifies `3(k − q) ≤ k + q`, i.e. `x ≤ 1/3`. Then `Λ(p^j) = (log p^j)/j`, and
`a_k = |Λ(k) − 1|` is bounded on the side of `1` that the bounds determine (the checker fails if
they straddle `1`).

**Square roots.** Newton's iteration from the previous `sq`; the checker verifies
`x² ≤ k·10^30 ≤ (x+1)²`, so `10^15/(x+1) ≤ 1/√k ≤ 10^15/x`.

**Sums.** Directed rounding: lower sums add floors, upper sums add floor + 1. `A(n) ≤ 2(n − 1)` is
checked (as `S·A(n)` upper bound `≤ 2(n−1)S`) at every `n`. The total rounding error is below
`10^-13`; the widths at `2^20` are about `1.1·10^-18` for `G` and `2.0·10^-14` for `H`.

## What the kernel checks

* `RSBounds/LambdaCert/Defs.lean`: the checker. `Nat`/`Bool` only; its loops are structural
  recursion (`Nat.rec`, `List.foldr`); no `Fin`; no Mathlib import. The arithmetic on literals is
  done by the kernel's `Nat` extensions.
* `RSBounds/LambdaCert/Segs/Seg00–15.lean`: 292 theorems `checkSeg st(i−1) st(i) = true`, each by
  `decide +kernel`. `checkSeg a b` builds the segment's masks, runs the steps from `a`, and compares
  the result field by field with `b`.
* `RSBounds/LambdaCert/Tables.lean`: `decide +kernel` checks that the 172 elements of `smallPrimes`
  are prime and that every prime `≤ 1024` is among them (trial division, with a soundness proof),
  and that `hpList` is sound (each `(q, p, j)` has `p ∈ smallPrimes`, `p^j = q`) and complete
  (contains every `p^j ≤ 2^20`, `j ≥ 2`).
* Final comparisons of the checkpoint states against `ghTable`, by `decide +kernel` on `Nat`
  inequalities.

## Soundness theorems (proved once)

* `Masks.lean`: bits of the masks (`testBit` of the geometric patterns, both directions), hence
  `MaskFacts`: an unset sieve bit gives `Nat.Prime k`, and a set sieve bit with an unset `hpList`
  bit gives `¬ IsPrimePow k` (for `2 ≤ k ≤ 2^20`).
* `LogSeries.lean`: `logRatio_sound`, the enclosure of `S(log k − log q)`.
* `Sound.lean`: the invariant `Inv`, preserved by one step (`inv_advance`), by a segment
  (`inv_runSeg`, `inv_checkSeg`), and true initially (`inv_init`). It connects the fixed-point
  numbers to `Λ` through `vonMangoldt_apply_prime`, `vonMangoldt_apply_pow` and
  `vonMangoldt_eq_zero_iff`, and to `Real.sqrt` and `Real.log`.
* `LambdaInputsProof.lean`: the chain `inv0 … inv292`, then both theorems.

## What is trusted

* The Lean kernel, including its GMP implementation of `Nat.add`, `sub`, `mul`, `div`, `mod`,
  `pow`, `ble`, `beq`, `land`, `lor`, `shiftLeft`, `shiftRight`, which the 292 segment checks rely on.
* The statement file and the Mathlib definitions it uses (`ArithmeticFunction.vonMangoldt`,
  `Real.log`, `Real.sqrt`, `Finset.sum`). The Mathlib lemmas used are kernel-checked like
  everything else.
* Not trusted: `tools/generate.py`. It is an exact Python mirror of `checkSeg`, used only to write
  the literal states in `States.lean` (and the generated `Segs/*` and `LambdaInputsProof.lean`); the
  kernel recomputes every state. `tools/reference_check.py` is an independent 50-digit decimal
  cross-check, not used by the proof. It reproduces the handover's numbers: minimal relative margin
  of `A(n) ≤ 2(n−1)` `0.07846` at `n = 1045573`, every table bound at least `1.00035·10^-6` from the
  value.

## Layout

```
RSBounds/LambdaInputs.lean          statements (unchanged)
RSBounds/LambdaInputsProof.lean     weightSumBound, ghBounds (generated)
RSBounds/LambdaCert/Defs.lean       the checker (Nat only)
RSBounds/LambdaCert/Tables.lean     smallPrimes, hpList: kernel checks + soundness
RSBounds/LambdaCert/Masks.lean      sieve-mask soundness
RSBounds/LambdaCert/LogSeries.lean  logarithm-series soundness
RSBounds/LambdaCert/Sound.lean      invariant and step/segment soundness
RSBounds/LambdaCert/States.lean     the 293 states (generated)
RSBounds/LambdaCert/Segs/*.lean     the 292 kernel checks (generated)
LambdaChallenge.lean, comparator.json   lake comparator setup
tools/generate.py                   regenerates States, Segs, LambdaInputsProof
tools/reference_check.py            independent decimal cross-check
logs/                               build log, axioms, comparator logs
```

To move the files into RSBounds: copy `RSBounds/LambdaCert/` and `RSBounds/LambdaInputsProof.lean`.
Auxiliary declarations live in `TernaryGoldbach.RSBounds.LambdaInputs.Cert`.
