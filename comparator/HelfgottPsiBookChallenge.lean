import Mathlib

/- [H, (2.14)] and [H, (2.17)] with Helfgott's constants on the book's ranges
(H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2), and the three unconditional
statements on finite ranges that the proof adds. Only the challenge contains deliberate theorem
holes; the solution is checked against the standard-three-axiom whitelist. The definitions are
compared with the solution's. -/

namespace TernaryGoldbach.RSBounds.Goals

def FiniteRH (A : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    |ρ.im| ≤ A → ρ.re = 1 / 2

end TernaryGoldbach.RSBounds.Goals

namespace TernaryGoldbach.RSBounds.HelfgottPsiBookComparator

/-- [H, (2.14)], ψ form, for `y ≥ 2·10⁶`. -/
theorem psi_le_10004 (hRH : Goals.FiniteRH 1894438.5122) {y : ℝ} (hy : 2e6 ≤ y) :
    Chebyshev.psi y ≤ 1.0004 * y := by sorry

/-- [H, (2.14)] for `y ≥ 2·10⁶`. -/
theorem sum_vonMangoldt_le_a14 (hRH : Goals.FiniteRH 1894438.5122) {y : ℝ} (hy : 2e6 ≤ y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 1.0004 * y := by sorry

/-- [H, (2.17)] for `y > 1.6·10⁶`. -/
theorem sum_vonMangoldt_mul_lt_a17 (hRH : Goals.FiniteRH 1894438.5122) {y : ℝ}
    (hy : 1.6e6 < y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * n <
      1.0008 * y ^ 2 / 2 := by sorry

/-- Unconditional: `ψ(y) ≤ 1.0004 y` for `2·10⁶ ≤ y ≤ 4·10⁶`. -/
theorem psi_le_10004_small {y : ℝ} (h1 : 2000000 ≤ y) (h2 : y ≤ 4000000) :
    Chebyshev.psi y ≤ 1.0004 * y := by sorry

/-- Unconditional: `∑_{n ≤ y} Λ(n) ≤ 1.0004 y` for `2·10⁶ ≤ y ≤ 4·10⁶`. -/
theorem sum_vonMangoldt_le_small {y : ℝ} (h1 : 2000000 ≤ y) (h2 : y ≤ 4000000) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 1.0004 * y := by sorry

/-- Unconditional: `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `1.6·10⁶ < y ≤ 2.5·10⁷`. -/
theorem sum_vonMangoldt_mul_lt_small {y : ℝ} (h1 : 1600000 < y) (h2 : y ≤ 25000000) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * n <
      1.0008 * y ^ 2 / 2 := by sorry

end TernaryGoldbach.RSBounds.HelfgottPsiBookComparator
