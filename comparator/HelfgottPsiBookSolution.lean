import RSBounds.HelfgottPsiBoundsBook

/- The theorems of `HelfgottPsiBookChallenge`, from the project's proofs. -/

open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.HelfgottPsiBookComparator

/-- [H, (2.14)], ψ form, for `y ≥ 2·10⁶`. -/
theorem psi_le_10004 (hRH : Goals.FiniteRH 1894438.5122) {y : ℝ} (hy : 2e6 ≤ y) :
    Chebyshev.psi y ≤ 1.0004 * y :=
  HelfgottPsiBoundsBook.psi_le_10004 hRH hy

/-- [H, (2.14)] for `y ≥ 2·10⁶`. -/
theorem sum_vonMangoldt_le_a14 (hRH : Goals.FiniteRH 1894438.5122) {y : ℝ} (hy : 2e6 ≤ y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 1.0004 * y :=
  HelfgottPsiBoundsBook.sum_vonMangoldt_le_a14 hRH hy

/-- [H, (2.17)] for `y > 1.6·10⁶`. -/
theorem sum_vonMangoldt_mul_lt_a17 (hRH : Goals.FiniteRH 1894438.5122) {y : ℝ}
    (hy : 1.6e6 < y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * n <
      1.0008 * y ^ 2 / 2 :=
  HelfgottPsiBoundsBook.sum_vonMangoldt_mul_lt_a17 hRH hy

/-- Unconditional: `ψ(y) ≤ 1.0004 y` for `2·10⁶ ≤ y ≤ 4·10⁶`. -/
theorem psi_le_10004_small {y : ℝ} (h1 : 2000000 ≤ y) (h2 : y ≤ 4000000) :
    Chebyshev.psi y ≤ 1.0004 * y :=
  _root_.RSBounds.HelfgottSmall.psi_le_10004_small h1 h2

/-- Unconditional: `∑_{n ≤ y} Λ(n) ≤ 1.0004 y` for `2·10⁶ ≤ y ≤ 4·10⁶`. -/
theorem sum_vonMangoldt_le_small {y : ℝ} (h1 : 2000000 ≤ y) (h2 : y ≤ 4000000) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 1.0004 * y :=
  _root_.RSBounds.HelfgottSmall.sum_vonMangoldt_le_small h1 h2

/-- Unconditional: `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `1.6·10⁶ < y ≤ 2.5·10⁷`. -/
theorem sum_vonMangoldt_mul_lt_small {y : ℝ} (h1 : 1600000 < y) (h2 : y ≤ 25000000) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * n <
      1.0008 * y ^ 2 / 2 :=
  _root_.RSBounds.HelfgottSmall.sum_vonMangoldt_mul_lt_small h1 h2

end TernaryGoldbach.RSBounds.HelfgottPsiBookComparator
