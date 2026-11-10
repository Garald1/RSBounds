# MoebiusCert: kernel-checked proofs of (M) and (m)

This project proves, at the pins of RSBounds (Lean `v4.35.0`, Mathlib `56a005855e…`), the two
hypotheses of `mobius003.tex` stated in `RSBounds/MoebiusInputs.lean` (unchanged, sha256
`c89825262727973898858a94fcf91af839b429f3e6c45bcaa7b4599215ea3d1f`):

```lean
theorem TernaryGoldbach.RSBounds.MoebiusInputs.mertensSqrt : MertensSqrt       -- (M)
theorem TernaryGoldbach.RSBounds.MoebiusInputs.smallMoebiusSum : SmallMoebiusSum -- (m)
```

Both are in `MoebiusCert/Final.lean`. `#print axioms` shows only `propext`, `Classical.choice`,
`Quot.sound` (see `logs/axioms.txt`). There is no `native_decide`, `sorry`, or new axiom; every
computation is `decide +kernel` on a `Bool`-valued checker over `Nat`/`Int`.

## Method

### Computing μ on a segment without per-integer kernel work

The kernel is slow per reduction step (≈ 5 μs for a `Nat.rec` step) but its `Nat` arithmetic is
GMP-accelerated, including `land`, `lor`, `xor`, shifts. All per-integer work is therefore done
bit-parallel on big naturals ("packed numbers" `pk w f n = ∑_{i<n} f i · 2^(w i)`): field `i`
holds data for the integer `L + i` of the segment `[L, L + 2^K)`.

* **Small primes** `p < 1000` (168 of them): an 8-bit-field accumulator `V` gets weight
  `a_p = 2ℓ_p + 1` at each multiple of `p`, where `2^ℓ_p ≤ p² < 2^(ℓ_p+1)`. The pattern for `p` is
  built by binary doubling (`repB`).
* **Medium primes** `1000 < p ≤ 31622` (3233): only a saturating 2-bit counter
  `(≥1, ≥2)` of how many divide `L + i`, kept as two 1-bit-layout bit planes updated by `|||`/`&&&`.
  This is 8× cheaper per prime than an 8-bit field and is the bulk of the cost.
* **Squares** `p² ∣ L + i`, `p ≤ 31622`: a 1-bit plane, `|||`-accumulated (most patterns empty).
* The 1-bit planes are moved to the 8-bit layout by a Morton spread (`log₂ S` mask/shift levels).
* **Decode**: with `λ = ⌊log₂ n⌋` constant on the segment, `μ(n) + 1 ∈ {0,1,2}` is computed fieldwise
  by a few bitwise operations from `V`, the counter and the square flag, comparing `V` with the
  thresholds `θ₀ = 5λ − 69`, `θ₁ = 5λ − 119`.

Why this is μ (`MoebiusCert/NT.lean`, `mu_core`): for squarefree `n ≤ 1000014128 < 31623²`,
let `s` be the product of its prime factors below 1000, `k` their number, `A = ∑ ℓ_p`, `v = 2A + k`,
`c` the number of medium prime factors and `b` the number of prime factors `> 31622`. Then `b ≤ 1`,
`c ≤ 2`, `c = 2 ⇒ b = 0`, and `μ(n) = (−1)^(k+c+b)`, `v ≡ k (mod 2)`. From `2^A ≤ s² ≤ 2^(A+k)` and
`2k ≤ A` one gets `3v + 5e ≥ 10λ` when `n ≤ sK` with `K² ≤ 2^e`, and `2v + 5e ≤ 10λ + 5` when
`sK ≤ n` with `2^e ≤ K²`. With `(K, e) = (1, 0), (31623, 29)` (case `c = 0`) and
`(31622, 30), (1001·31623, 49)` (case `c = 1`) this gives `b = 1 ⇔ v < θ_c` for `λ ≤ 29`.

`MoebiusCert/Bridge.lean` (`segMu1_eq`) proves that the kernel function `segMu1` returns exactly
`pk 8 (fun i => (μ (L+i) + 1).toNat) (2^K)`.

### (M): `10⁶ M(n)² ≤ 326041 n` for `33 ≤ n ≤ 10⁹`

* `n < 2^18`: 75 segments, per-element loop (`smallCheck`) with the exact integer inequality.
* `2^18 ≤ n ≤ 1000013823`: 3815 segments (`[j·2^18, (j+1)·2^18)` for `1 ≤ j ≤ 3813`, then
  `2^17` and `2^16` pieces). Per segment (`largeCheck`): the `μ+1` fields are summed in groups of 4
  into 32-bit fields, prefix sums are taken by a doubling scan, and a single guard-bit test checks
  `|M(L + 4j + 3)| ≤ B − 2` for all group ends, where `B` (data) satisfies `10⁶B² ≤ 326041 L`
  (checked). Every `n` of the segment is within 2 of a group end, so `|M(n)| ≤ B`, and
  `10⁶ M(n)² ≤ 10⁶ B² ≤ 326041 L ≤ 326041 n`. Here `B = ⌊√(326041 L/10⁶)⌋`; the smallest slack
  `B − max_{segment}|M|` over the full segments in `[2^18, 10⁹]` is 34, at `L = 2^18`
  (`tools/slack.c`, not part of the proof).
* Data: `M(L−1)` at each segment start and `B`; each segment's theorem also checks the value at its
  end, so the data are certified by the chain (`SegGood.trans_eq`), starting from `M(0) = 0`.

### (m): `|m(n)| log(n+1) ≤ 0.03` for `11815 ≤ n ≤ 6·10⁵`

Per-element loop (`msCheck`, 158 segments up to `602111`) keeping integers `lo ≤ 10²⁰·m(k) ≤ hi`,
adding `⌊10²⁰/k⌋` or `⌈10²⁰/k⌉` with the appropriate direction, and an exponent `e` with
`(k+1)^16 ≤ 2^e` (so `log(k+1) ≤ (e/16) log 2`). For `k ≥ 11815` it checks
`max(|lo|,|hi|) · e · 6931471808 ≤ 48 · 10²⁰ · 10⁸`, which with Mathlib's
`Real.log_two_lt_d9 : log 2 < 0.6931471808` gives the bound. The checked quantity comes closest to
its bound at `k = 11815`, at 98.6% (the enclosure `log(k+1) ≤ (e/16) log 2` loses a little there;
the true maximum of `|m(n)| log(n+1)` is `0.029496`, at `n = 11820`, as stated in the statement file).
The data `(lo, hi, e)` at the segment boundaries are produced by `tools/gen_data.py`, which runs the
same recurrence in Python.

## What the kernel checks, and what is trusted

* Trusted: the Lean kernel (with its GMP `Nat` acceleration), and the statement file together with
  the Mathlib definitions it uses (`ArithmeticFunction.moebius`, `Finset.Icc`, `Real.log`, …).
  `decide +kernel` evaluates the checkers in the kernel only; neither the elaborator's evaluator
  nor compiled code is involved.
* Kernel-checked computations: the prime data (`MoebiusCert/Primes.lean`: `spData`/`mpData` are
  exactly the primes `< 1000` and in `(1000, 31622]`, by trial division, plus the weight
  inequalities), and one `Bool` check per segment (`MoebiusCert/Large`, `Small`, `Ms`).
* Everything else is proved: the packed-number library (`Pack.lean`), soundness of every kernel
  function (`Sieve.lean`: repunits, patterns, passes, Morton spread, decode, grouping, scan, band
  check), the number theory (`NT.lean`), and the chaining (`Segments.lean`, `SmallSeg.lean`,
  `MsSeg.lean`, `Agg/`, `Final.lean`).
* The segment data in `tools/segments.json` (and the generator `tools/gen_modules.py`) are not
  trusted: a wrong value makes a segment check fail.

## Layout

| Path | Contents |
|---|---|
| `RSBounds/MoebiusInputs.lean` | the statements (unchanged) |
| `MoebiusCert/PrimeData.lean`, `Defs.lean`, `DefsSmall.lean` | kernel-evaluated data and checkers (no Mathlib) |
| `MoebiusCert/Pack.lean`, `Raw.lean`, `Sieve.lean` | packed numbers; soundness of the kernel functions |
| `MoebiusCert/NT.lean`, `Primes.lean`, `Bridge.lean` | μ from the sieve data; prime certificates; `segMu1_eq` |
| `MoebiusCert/Segments.lean`, `SmallSeg.lean`, `MsSeg.lean` | segment soundness |
| `MoebiusCert/Large/`, `Small/`, `Ms/` | generated segment checks (`decide +kernel`) |
| `MoebiusCert/Agg/`, `Final.lean` | generated chaining; the two theorems |
| `tools/` | C/Python cross-checks, data and module generators |

`MoebiusCert/LargeAll.lean`, `SmallAll.lean`, `MsAll.lean` are convenience roots importing only the
segment modules (not needed by `lake build`).

Segment modules set `Elab.async false`: otherwise Lean checks the theorems of a module in parallel
and the peak memory multiplies (each large segment needs ≈ 1.7 GB).

## Build

`logs/build.log` is a from-scratch `lake build` of a fresh copy of exactly these sources (Mathlib and
its dependencies were taken prebuilt from the Mathlib cache, `lake exe cache get`), on a 2-core
machine with a ≈ 5.9 GB memory limit (lake ran 2 jobs). Summary (`logs/build_summary.txt`):

* 1042 project modules: 954 large-mode segment modules (4 segments each), 10 `(M)` and 20 `(m)`
  per-element modules (8 segments each), 42 aggregators, 12 library modules, `Final`, the root
  `MoebiusCert`, and `RSBounds.MoebiusInputs` with its root `RSBounds`; 0 errors.
* Wall time 63 min 40 s; CPU time 109.1 min user + 16.6 min sys ≈ 2.10 core-hours, of which the
  large-mode segment modules are 1.96 core-hours (≈ 1.85 s per segment of `2^18` integers).
* Peak memory per `lean` process ≈ 1.8 GB (large segments); allow ≈ 2 GB per lake job.

The remaining warnings in the log are deprecation warnings (`if_pos`, `Int.ofNat_eq_coe`, …), unused
variables, and Mathlib's "designed for use with the module system" notices (also emitted for the
statement file).

## Checks done

* `#print axioms` (`logs/axioms.lean`, output in `logs/axioms.txt`):
  `[propext, Classical.choice, Quot.sound]` for both theorems.
* `RSBounds/MoebiusInputs.lean` has sha256 `c89825262727973898858a94fcf91af839b429f3e6c45bcaa7b4599215ea3d1f`.
* No `sorry`, `native_decide`, `axiom`, `implemented_by`, `extern` or `debug.skipKernelTC` in the
  sources; the only options set are `maxRecDepth` and `Elab.async`.
* A leanprover/comparator run was **not** done: no sandbox (bubblewrap/landrun) was available on the
  machine used.

## Reproducing

```
lake exe cache get    # prebuilt Mathlib
lake build            # builds RSBounds and MoebiusCert
lake env lean logs/axioms.lean
```
Regenerating the data: `gcc -O2 -o tools/mertens_at tools/mertens_at.c -lm`,
`python3 tools/gen_data.py`, `python3 tools/gen_modules.py`.
