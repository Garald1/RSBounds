# [H] (2.16), (2.18) and (2.19) on the book's ranges: the walk below 2·10⁶

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2, §2.3, states

* (2.16) `∑_{n≤y} Λ(n) n < 1.03884 y²/2` for `y > 663`;
* (2.18) `∑_{n≤y} Λ(n)/√n < 2 · 1.0004 √y` for `y ≥ 1`;
* (2.19) `∑_{y/2<p≤y} (log p)² ≤ ½ y log y` for `y ≥ 117`.

`RSBounds/HelfgottLow/` proves them, with no hypothesis, up to `2·10⁶`, and extends them to the
book's ranges given the large-`y` inputs as hypotheses:

| theorem (`RSBounds.HelfgottLow`) | statement | range | hypothesis |
|---|---|---|---|
| `sum_vonMangoldt_mul_lt_a16_small` | (2.16) | `663 < y ≤ 1.6·10⁶` | none |
| `sum_vonMangoldt_mul_lt_a16_of` | (2.16) | `y > 663` | (2.17) for `y > 1.6·10⁶` |
| `sum_vonMangoldt_div_sqrt_lt_small` | (2.18) | `1 ≤ y < 2·10⁶ + 1` | none |
| `sum_vonMangoldt_div_sqrt_lt_of` | (2.18) | `y ≥ 1` | (2.14) for `y ≥ 2·10⁶` |
| `sum_log_sq_primes_le_small` | (2.19) | `117 ≤ y < 2·10⁶ + 1` | none |
| `sum_log_sq_primes_le_of` | (2.19) | `y ≥ 117` | (2.19) for `y ≥ 2·10⁶` |

The hypotheses are stated as `HelfgottPsiBoundsBook` proves (2.17) and (2.14), so
`RSBounds/HelfgottLowBook.lean` gets (2.16) and (2.18) on the book's ranges under
`FiniteRH 1894438.5122` alone (`sum_vonMangoldt_mul_lt_a16`, `sum_vonMangoldt_div_sqrt_lt_a18`).
(2.19) is stated exactly as `TernaryGoldbach.Prelim.sum_log_sq_primes_le` (calr3/ternary-goldbach,
`y ≥ 2·10⁶`), so that theorem is the hypothesis of `sum_log_sq_primes_le_of`; RSBounds does not
import it.

None of the ranges can start lower: (2.16) fails at `y = 662` and (2.19) at `y = 116`.

## Margins (floating point, `scripts/margins_low.py`)

* (2.16) on `[663, 1.6·10⁶]`: the smallest relative slack is 0.29%, at `y = 663`.
* (2.18) on `[2, 2·10⁶]`: 0.12%, at `y = 1 948 801` (3.38 in absolute terms).
* (2.19) on `[117, 2·10⁶]`: 0.44%, at `y = 199`.
* The summation by parts above `2·10⁶` needs
  `∑_{n ≤ 2·10⁶} Λ(n) (1/√n − 1/√(2·10⁶)) < 1.0004 √(2·10⁶)`: the left side is 1411.52 and the
  right side 1414.78.

The walk's own upper bounds lose 0.62 in `ψ(2·10⁶)` and 0.004 in `∑_{n ≤ 2·10⁶} Λ(n)/√n`.

## Method

A walk over `n = 2, …, 2 000 000` (`Defs.lean`), in `Nat` arithmetic scaled by `SC = 10¹⁵`, keeps
upper bounds for `∑_{m≤n} Λ(m)`, `∑_{m≤n} Λ(m) m`, `∑_{m≤n} Λ(m)/√m` and (scaled by `SC²`)
`∑ (log m)²` over the possible primes `m ∈ (⌊n/2⌋, n]`, and checks the three inequalities at every
`n` in range.

* Possible primes, prime-power events and the upper bound `log n ≤ log a + (n − a)/a` are those
  of `HelfgottSmall` (`docs/HelfgottSmall.md`), whose lemmas are reused (`vonMangoldt_le_inc`).
* The 2 161 anchors `(a, l, lo, r)` carry, besides `log a ≤ l/SC`, a lower bound
  `lo/SC ≤ log a` and an upper bound `SC/√a ≤ r`. The lower bounds go by induction from
  Mathlib's `log 2 > 0.6931471803`, with `e^u ≤ ∑_{i≤8} u^i/i! + 10u⁹/(9·9!)` for `0 ≤ u ≤ 1`
  (`Real.exp_bound'`) at each step; `SC² ≤ r²a` is checked for every anchor (`DataChecks.lean`).
* `log n ≥ log a + (n − a)/n` (lower bound) and `1/√n ≤ (1/√a)(a + n)/(2n)` (AM–GM) between
  anchors (`lowW_le`, `inv_sqrt_le`).
* The window `(⌊n/2⌋, n]` of (2.19) is kept by a second pointer at `n/2` with its own anchor:
  a possible prime leaving the window is removed with a lower bound for its `(log m)²`, so the
  window sum stays an upper bound.
* The anchors still to come are kept in the state as a list, so moving to the next anchor costs
  nothing; chunk boundaries record only the anchors' numbers (`attach`).
* The walk also keeps an upper bound for `∑_{m≤n} Λ(m)(1/√m − ρ₀)`, `ρ₀ = ⌊SC/√(2·10⁶+1)⌋/SC`;
  its final value gives the bound that the summation by parts above `2·10⁶` starts from
  (`finalB`, `bS_N0`, `tS_lt_of_psi`).

`Walk.lean` proves that a successful walk keeps its invariant (`walk_inv`). The walk is cut into
200 chunks of 10 000 positions, one per module (`Chunk/C0000.lean` …), each checked by
`decide +kernel`; a chunk takes about 8 s and 1.4 GB. Python (`scripts/gen_helfgott_low.py`) only
produces candidate data (anchors and chunk boundaries); rerunning it reproduces every generated
file.

## Build

```sh
lake build RSBounds.HelfgottLow.Final HelfgottLowSolution
```

About 15 minutes on 2 cores. `RSBounds/HelfgottLowBook.lean` needs `HelfgottPsiBoundsBook`, that is
the full tree (PsiCert), and is built with

```sh
lake build RSBounds.HelfgottLowBook
```

`comparator-helfgott-low.json` checks the six theorems of the table; the solution imports only
`RSBounds.HelfgottLow.Final`. `run-helfgott-low.sh` builds everything, including
`RSBounds.HelfgottLowBook`, checks that all eight theorems use only `propext`, `Classical.choice`
and `Quot.sound`, and runs Comparator. On 2026-11-17 it passed on the full tree: Comparator
reported "Your solution is okay!" after 19 min 28 s.
