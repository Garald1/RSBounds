import RSBounds.HelfgottAppA.EtaPlusSup
import TernaryGoldbach.Helfgott.NonPrime

/-!
# [H] (14.51) with Helfgott's constant `7.3306`

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2, (14.51): for
`N ≥ 10²⁷`, the terms of the weighted count of `n₁ + n₂ + n₃ = N` in which some `nᵢ` is even or
not prime contribute at most `7.3306 N^{3/2} log N`. [H] gets
`7.3306 ≥ 3 · 1.079955² · 1.414 · 1.4263 · 1.03883` from `|η₊|_∞ ≤ 1.079955` (14.3),
`|η_*|_∞ ≤ 1.414` (14.21), `ψ(x) < 1.03883 x` and `ψ(x) − θ(x) < 1.4262 √x` [RS62, Thms 12, 13].

Here the reduction is calr3/ternary-goldbach's `repSum_sub_le_of_bounds`, with the constants as
parameters, and `|η₊| ≤ 1.079955` is `abs_etaPlus_le_1079955` (`EtaPlusSup.lean`). The other three
inputs are hypotheses, stated as calr3's current main proves them: `hAs` (`|η_*| ≤ 1.414`,
`Helfgott.abs_etaStar_le_1414`; not yet in the calr3 revision RSBounds pins), `hpsi` and `h55`
(`Prelim.psi_bounds`, `Prelim.sum_vonMangoldt_nonprime_lt`, from `PlattGRH`).
-/

open Real Finset
open scoped ArithmeticFunction.vonMangoldt

namespace RSBounds.HelfgottAppA

open TernaryGoldbach.Helfgott (repSum psi theta etaStar ΛBad_nonneg sum_ΛBad_le
  repSum_sub_le_of_bounds)

theorem range_succ_eq_insert (N : ℕ) : range (N + 1) = insert 0 (Icc 1 N) := by
  ext n; simp only [mem_range, mem_insert, mem_Icc]; omega

theorem psi_eq_sum_Icc (N : ℕ) : psi N = ∑ m ∈ Icc 1 N, (Λ m : ℝ) := by
  unfold TernaryGoldbach.Helfgott.psi
  rw [range_succ_eq_insert, sum_insert (by simp)]
  simp

theorem psi_sub_theta_eq (N : ℕ) :
    psi N - theta N = ∑ n ∈ Icc 1 N, (if n.Prime then 0 else (Λ n : ℝ)) := by
  classical
  unfold TernaryGoldbach.Helfgott.psi TernaryGoldbach.Helfgott.theta
  rw [← sum_sub_distrib, range_succ_eq_insert, sum_insert (by simp)]
  simp only [ArithmeticFunction.map_zero, Nat.not_prime_zero, ite_false, sub_self, zero_add]
  refine sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- **[H, (14.51)]**: the terms where some `nᵢ` is even or not prime contribute at most
`7.3306 · N^{3/2} log N`, for `N ≥ 10²⁷`, given `ψ(n) ≤ 1.03883 n` and `ψ(y) − θ(y) < 1.4262 √y`
([RS62, Thms 12, 13]). -/
theorem nonprime_input_book
    (hAs : ∀ t : ℝ, 0 ≤ t → |etaStar t| ≤ 1.414)
    (hpsi : ∀ n : ℕ, ∑ m ∈ Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y → ∑ n ∈ Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    (N : ℕ) (hN27 : 10 ^ 27 ≤ N) :
    repSum (fun _ => True) N - repSum (fun n => n.Prime ∧ Odd n) N ≤
      7.3306 * (N * √N) * Real.log N := by
  have hN : 1 ≤ N := le_trans (by norm_num) hN27
  have h := repSum_sub_le_of_bounds hN (fun t ht => abs_etaPlus_le_1079955 ht)
    hAs
  have hpsi : psi N ≤ 1.03883 * N := by
    rw [psi_eq_sum_Icc]; exact hpsi N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpt : psi N - theta N < 1.4262 * √N := by
    have := h55 N hNpos
    rwa [Nat.floor_natCast, ← psi_sub_theta_eq] at this
  have hNr : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN27
  have hsq : (10 : ℝ) ^ 13 ≤ √N := Real.le_sqrt_of_sq_le (by nlinarith)
  have hlog2 : Real.log 2 ≤ 0.0001 * √N := by
    have := Real.log_two_lt_d9; nlinarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hbad0 : 0 ≤ psi N - theta N + Real.log 2 :=
    (Finset.sum_nonneg fun n _ => ΛBad_nonneg n).trans (sum_ΛBad_le N)
  have hpsi0 : 0 ≤ psi N := Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  calc repSum (fun _ => True) N - repSum (fun n => n.Prime ∧ Odd n) N
      ≤ 3 * (1.079955 ^ 2 * 1.414) * Real.log N * (psi N - theta N + Real.log 2) * psi N := h
    _ ≤ 3 * (1.079955 ^ 2 * 1.414) * Real.log N * (1.4263 * √N) * (1.03883 * N) := by
        gcongr; linarith
    _ = (3 * (1.079955 ^ 2 * 1.414) * 1.4263 * 1.03883) * (N * √N) * Real.log N := by ring
    _ ≤ 7.3306 * (N * √N) * Real.log N := by gcongr; norm_num

end RSBounds.HelfgottAppA
