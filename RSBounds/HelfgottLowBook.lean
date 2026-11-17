import RSBounds.HelfgottPsiBoundsBook
import RSBounds.HelfgottLow.Final

/-!
# [H, (2.16)] and [H, (2.18)] on the book's ranges

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2, §2.3. [H] states (2.16),
`∑_{n ≤ y} Λ(n) n < 1.03884 y²/2`, for `y > 663`, and (2.18), `∑_{n ≤ y} Λ(n)/√n < 2 · 1.0004 √y`,
for `y ≥ 1`. Up to `2·10⁶` both come from the unconditional, kernel-checked walk of `HelfgottLow`
(see `docs/HelfgottLow.md`); above it, (2.16) follows from (2.17) and (2.18) from (2.14) by
summation by parts. (2.14) and (2.17) are `HelfgottPsiBoundsBook`'s, so the only premise is
`FiniteRH 1894438.5122`, as there.

[H] (2.19) for `117 ≤ y < 2·10⁶ + 1` is `RSBounds.HelfgottLow.sum_log_sq_primes_le_small`
(unconditional); with `TernaryGoldbach.Prelim.sum_log_sq_primes_le` (`y ≥ 2·10⁶`) it gives
the book's range through `RSBounds.HelfgottLow.sum_log_sq_primes_le_of`.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.HelfgottLowBook

open Goals

/-- **[H, (2.16)]**: `∑_{n ≤ y} Λ(n) n < 1.03884 y²/2` for `y > 663`. -/
theorem sum_vonMangoldt_mul_lt_a16 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 663 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.03884 * y ^ 2 / 2 :=
  _root_.RSBounds.HelfgottLow.sum_vonMangoldt_mul_lt_a16_of
    (fun _ h => HelfgottPsiBoundsBook.sum_vonMangoldt_mul_lt_a17 hRH h) hy

/-- **[H, (2.18)]**: `∑_{n ≤ y} Λ(n)/√n < 2 · 1.0004 √y` for `y ≥ 1`. -/
theorem sum_vonMangoldt_div_sqrt_lt_a18 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / √(n : ℝ) < 2 * 1.0004 * √y :=
  _root_.RSBounds.HelfgottLow.sum_vonMangoldt_div_sqrt_lt_of
    (fun _ h => HelfgottPsiBoundsBook.sum_vonMangoldt_le_a14 hRH h) hy

end TernaryGoldbach.RSBounds.HelfgottLowBook
