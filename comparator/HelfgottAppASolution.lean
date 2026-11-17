import RSBounds.HelfgottAppA.EBound

/- The theorems of `HelfgottAppAChallenge`, from the project's proofs. -/

open scoped ArithmeticFunction.vonMangoldt
open TernaryGoldbach.Helfgott

namespace TernaryGoldbach.RSBounds.HelfgottAppAComparator

/-- [H, (14.3)]: `|η₊(t)| ≤ 1.079955` for `t ≥ 0`. -/
theorem abs_etaPlus_le_1079955 {t : ℝ} (ht : 0 ≤ t) : |etaPlus t| ≤ 1.079955 :=
  _root_.RSBounds.HelfgottAppA.abs_etaPlus_le_1079955 ht

/-- [H, (14.24)]: `t |η₊(t)| ≤ 1.19073` for `t ≥ 0`. -/
theorem mul_abs_etaPlus_le_119073 {t : ℝ} (ht : 0 ≤ t) : t * |etaPlus t| ≤ 1.19073 :=
  _root_.RSBounds.HelfgottAppA.mul_abs_etaPlus_le_119073 ht

/-- [H, (14.51)] with `7.3306`, given `|η_*| ≤ 1.414` and [RS62, Thms 12, 13]. -/
theorem nonprime_input_book (hAs : ∀ t : ℝ, 0 ≤ t → |etaStar t| ≤ 1.414)
    (hpsi : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    repSum (fun _ => True) N - repSum (fun n => n.Prime ∧ Odd n) N ≤
      7.3306 * (N * √N) * Real.log N :=
  _root_.RSBounds.HelfgottAppA.nonprime_input_book hAs hpsi h55 N hN27

/-- [H, (14.28)], first form, given [RS62, Thms 12, 13]. -/
theorem E_le_book_formula (hpsi : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤
      (2.94325 * Real.log x + 5.12426) * √x :=
  _root_.RSBounds.HelfgottAppA.E_le_book_formula hpsi h55 hx

/-- [H, (14.28)], given [RS62, Thms 12, 13]. -/
theorem E_le_14_28_book (hpsi : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y →
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤ 8.4029e-12 * x :=
  _root_.RSBounds.HelfgottAppA.E_le_14_28_book hpsi h55 hx

end TernaryGoldbach.RSBounds.HelfgottAppAComparator
