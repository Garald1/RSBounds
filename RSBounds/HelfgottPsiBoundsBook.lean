import RSBounds.HelfgottPsiBoundsFinal
import RSBounds.HelfgottSmall.Final

/-!
# [H, (2.14)] and [H, (2.17)] on the book's ranges

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2. [H] states (2.14),
`∑_{n ≤ y} Λ(n) ≤ 1.0004 y`, for `y ≥ 2·10⁶`, and (2.17), `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2`, for
`y > 1.6·10⁶`. `HelfgottPsiBoundsFinal` proves them from `2.5·10⁷` (and `ψ(y) ≤ 1.0004 y` from
`4·10⁶`); the gap is closed by the unconditional, kernel-checked walk of `HelfgottSmall`
(see `docs/HelfgottSmall.md`). The only premise left is `FiniteRH 1894438.5122`, which the
ranges above `4·10⁶` and `2.5·10⁷` need.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.HelfgottPsiBoundsBook

open Goals

/-- **[H, (2.14)]**, ψ form: `ψ(y) ≤ 1.0004 y` for `y ≥ 2·10⁶`. -/
theorem psi_le_10004 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 2e6 ≤ y) :
    Chebyshev.psi y ≤ 1.0004 * y :=
  _root_.RSBounds.HelfgottSmall.psi_le_10004_of_ge
    (fun y h => HelfgottPsiBounds.psi_le_10004 Schoenfeld1976Final.psiCert hRH
      (by have e : (4e6 : ℝ) = 4000000 := by norm_num
          linarith))
    (by have e : (2e6 : ℝ) = 2000000 := by norm_num
        linarith)

/-- **[H, (2.14)]**: `∑_{n ≤ y} Λ(n) ≤ 1.0004 y` for `y ≥ 2·10⁶`. -/
theorem sum_vonMangoldt_le_a14 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 2e6 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y := by
  rw [HelfgottPsiBounds.sum_Icc_eq_psi]
  exact psi_le_10004 hRH hy

/-- **[H, (2.17)]**: `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y > 1.6·10⁶`. -/
theorem sum_vonMangoldt_mul_lt_a17 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 1.6e6 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 :=
  _root_.RSBounds.HelfgottSmall.sum_vonMangoldt_mul_lt_of_ge
    (fun y h => HelfgottPsiBoundsFinal.sum_vonMangoldt_mul_lt_a17 hRH
      (by have e : (2.5e7 : ℝ) = 25000000 := by norm_num
          linarith))
    (by have e : (1.6e6 : ℝ) = 1600000 := by norm_num
        linarith)

end TernaryGoldbach.RSBounds.HelfgottPsiBoundsBook
