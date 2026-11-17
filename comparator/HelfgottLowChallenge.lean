import Mathlib

/- [H] (2.16), (2.18) and (2.19) (H. A. Helfgott, *The ternary Goldbach problem*,
arXiv:1501.05438v2, §2.3): the unconditional statements on `y ≤ 2·10⁶` that the kernel-checked
walk gives, and the statements that extend them to the book's ranges given (2.17), (2.14) and
(2.19) above `2·10⁶` as hypotheses (in the forms of `comparator/HelfgottPsiBookChallenge.lean`
and of `TernaryGoldbach.Prelim.sum_log_sq_primes_le`). Only the challenge contains deliberate
theorem holes; the solution is checked against the standard-three-axiom whitelist. -/

namespace TernaryGoldbach.RSBounds.HelfgottLowComparator

/-- [H, (2.16)] for `663 < y ≤ 1.6·10⁶`, unconditionally. -/
theorem sum_vonMangoldt_mul_lt_a16_small {y : ℝ} (h1 : 663 < y) (h2 : y ≤ 1600000) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * n < 1.03884 * y ^ 2 / 2 := by sorry

/-- [H, (2.16)] for `y > 663`, given [H, (2.17)] for `y > 1.6·10⁶`. -/
theorem sum_vonMangoldt_mul_lt_a16_of (h17 : ∀ y : ℝ, 1.6e6 < y →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * n < 1.0008 * y ^ 2 / 2)
    {y : ℝ} (hy : 663 < y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * n < 1.03884 * y ^ 2 / 2 := by sorry

/-- [H, (2.18)] for `1 ≤ y < 2·10⁶ + 1`, unconditionally. -/
theorem sum_vonMangoldt_div_sqrt_lt_small {y : ℝ} (h1 : 1 ≤ y) (h2 : y < 2000001) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n <
      2 * 1.0004 * Real.sqrt y := by sorry

/-- [H, (2.18)] for `y ≥ 1`, given [H, (2.14)] for `y ≥ 2·10⁶`. -/
theorem sum_vonMangoldt_div_sqrt_lt_of (h14 : ∀ y : ℝ, 2e6 ≤ y →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 1.0004 * y)
    {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n <
      2 * 1.0004 * Real.sqrt y := by sorry

/-- [H, (2.19)] for `117 ≤ y < 2·10⁶ + 1`, unconditionally. -/
theorem sum_log_sq_primes_le_small {y : ℝ} (h1 : 117 ≤ y) (h2 : y < 2000001) :
    ∑ p ∈ (Finset.Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y := by sorry

/-- [H, (2.19)] for `y ≥ 117`, given it for `y ≥ 2·10⁶`. -/
theorem sum_log_sq_primes_le_of (hbig : ∀ y : ℝ, 2e6 ≤ y →
      ∑ p ∈ (Finset.Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y)
    {y : ℝ} (hy : 117 ≤ y) :
    ∑ p ∈ (Finset.Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y := by sorry

end TernaryGoldbach.RSBounds.HelfgottLowComparator
