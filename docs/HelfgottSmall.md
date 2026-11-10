# [H] (2.14) and (2.17) below 2.5·10⁷: the small-range walk

`RSBounds/HelfgottSmall/` proves, with no hypothesis at all,

| theorem (`RSBounds.HelfgottSmall`) | statement | range |
|---|---|---|
| `psi_le_10004_small` | `ψ(y) ≤ 1.0004 y` | `2·10⁶ ≤ y ≤ 4·10⁶` |
| `sum_vonMangoldt_le_small` | `∑_{1≤n≤⌊y⌋} Λ(n) ≤ 1.0004 y` | `2·10⁶ ≤ y ≤ 4·10⁶` |
| `sum_vonMangoldt_mul_lt_small` | `∑_{1≤n≤⌊y⌋} Λ(n) n < 1.0008 y²/2` | `1.6·10⁶ < y ≤ 2.5·10⁷` |

Together with the addon's `psi_le_10004` (from `4·10⁶`) and `sum_vonMangoldt_mul_lt_a17` (from
`2.5·10⁷`), these give (2.14) from `2·10⁶` and (2.17) from `1.6·10⁶`, the ranges of
[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2, (2.14) and (2.17).

## Margins (floating point, `scripts/helfgott_small_margins.py`)

* (2.14) on `[2·10⁶, 4·10⁶]`: the smallest slack `1.0004 y − ψ(y)` is 118.9, at `y = 2 275 771`.
* (2.17) on `(1.6·10⁶, 2.5·10⁷]`: the smallest slack `1.0008 y²/2 − ∑ Λ(n) n` is `3.1·10⁸`
  (that is `1.2·10⁻⁴ · y²/2`), also at `y = 2 275 771`.
* The last prime power at which either inequality fails is `1 518 589`, below the book's
  thresholds.

The walk's own upper bounds lose 0.7 of the 118.9 in (2.14).

## Method

A walk over `n = 2, …, 25 000 000` (`Defs.lean`), in `Nat` arithmetic scaled by `10¹⁵`, keeps
upper bounds for `∑_{m≤n} Λ(m)` and `∑_{m≤n} Λ(m) m` and checks both inequalities at every `n`
in range. Only upper bounds are needed, so nothing is proved prime:

* `n` counts as a possible prime if it passes trial division (`n ≤ 5000`) or is coprime to the
  product of the numbers `2 ≤ m ≤ 5000` that pass trial division (`n > 5000`). Every prime does
  (`isSurv_prime`).
* Prime powers `p^k`, `k ≥ 2`, come from a sorted list; the kernel checks that it contains every
  `m^k ≤ 2.5·10⁷` with `m` as above (`events_complete`).
* `log n ≤ log a + (n − a)/a` for the last anchor `a ≤ n`; the 2 667 anchors have
  `log a ≤ l / 10¹⁵`, by induction from Mathlib's `log 2 < 0.6931471808` and, at each step,
  `b/a ≤ ∑_{i≤8} u^i/i! ≤ e^u` (`anchors_chainOK`, `anchor_good`).

`Walk.lean` proves that a successful walk keeps its invariant (`walk_inv`). The walk is cut into
1 250 chunks of 20 000 positions, one per module (`Chunk/C0000.lean` …), each checked by
`decide +kernel`; a chunk takes about 15 s and 1.8 GB. Python (`scripts/gen_helfgott_small.py`)
only produces candidate data: the chunk boundaries and anchors.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Build

```sh
lake build RSBounds.HelfgottSmall.Final
```

On 2 cores this takes about three hours; on 12 cores, about half an hour. Peak memory is about
1.8 GB per parallel job.
