import TernaryGoldbach.Explicit.ZeroFree
import TernaryGoldbach.Explicit.Digamma

/-!
# Selective unchanged-body reuse of the Stechkin analytic APIs

Copyright (c) 2026 Charlie Reams and Harald Helfgott.
Source: calr3/ternary-goldbach, commit
ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0,
TernaryGoldbach/Explicit/ZeroFreeRegion.lean.
The four theorem texts below are unchanged. Only the containing namespace
and imports/context are isolated, to avoid depending on the later R=11
zero-free theorem in that file. See verification/rs75-stechkin-core-port.json
for literal fragment hashes, and licenses/calr3-ternary-goldbach-MIT.txt
for the original MIT license.
-/

open Complex Set Metric Filter MeasureTheory
open scoped Real Interval Topology ComplexConjugate ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.RS75StechkinCore

open TernaryGoldbach.Explicit

theorem re_term_vM (σ τ : ℝ) (n : ℕ) :
    (LSeries.term (fun n => (Λ n : ℂ)) ((σ : ℂ) + τ * I) n).re =
      if n = 0 then 0 else Λ n * Real.exp (-σ * Real.log n) * Real.cos (τ * Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, if_neg hn, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log, Complex.re_ofReal_mul]
  have e : (Real.log n : ℂ) * -((σ : ℂ) + τ * I) = ((-σ * Real.log n : ℝ) : ℂ) + ((-τ * Real.log n : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e, Complex.exp_re]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
    add_im, mul_im, zero_add]
  rw [show -τ * Real.log n = -(τ * Real.log n) by ring, Real.cos_neg]
  ring

theorem hasSum_re_vM {σ : ℝ} (hσ : 1 < σ) (τ : ℝ) :
    HasSum (fun n : ℕ => if n = 0 then 0 else Λ n * Real.exp (-σ * Real.log n) * Real.cos (τ * Real.log n))
      (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + τ * I)).re := by
  have hs : 1 < ((σ : ℂ) + τ * I).re := by simpa using hσ
  have h := Complex.hasSum_re (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum
  convert h using 1 <;> first | rfl | (funext n; rw [re_term_vM])

theorem re_vM_eq {s : ℂ} (hs : 1 < s.re) :
    (LSeries (fun n => (Λ n : ℂ)) s).re = -(logDeriv xiF s).re + (1 / s).re + (1 / (s - 1)).re -
      1 / 2 * Real.log π + 1 / 2 * (Complex.digamma (s / 2)).re := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [logDeriv_xiF (by linarith) hs1 (xiF_ne_zero_of_one_le_re hs.le), logDeriv_zetaF_eq hs1 hz,
    logDeriv_apply]
  have hl : (Complex.log (π : ℂ)).re = Real.log π := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.ofReal_re]
  rw [hL]
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, hl]
  norm_num
  rw [neg_div, Complex.neg_re]
  ring

theorem stechkin_xi_nonneg {s s1 : ℂ} (hs : 1 < s.re) (hss : s.re < s1.re) (him : s1.im = s.im)
    (h32 : 3 / 2 ≤ (s.re - 1 / 2) ^ 2 + (s1.re - 1 / 2) ^ 2) :
    0 ≤ (logDeriv xiF s).re - (s.re - 1 / 2) / (s1.re - 1 / 2) * (logDeriv xiF s1).re := by
  set κ := (s.re - 1 / 2) / (s1.re - 1 / 2) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (by linarith)
  have hs1 : 1 < s1.re := by linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set M := max ‖s - 1 / 2‖ ‖s1 - 1 / 2‖ with hM
  have hM0 : 0 ≤ M := le_max_of_le_right (norm_nonneg _)
  set ε' := ε / (2 * (1 + κ)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨T, -, happrox, -, hzero⟩ := xi_partial_approx hM0 hε'0
  have hp := pair_approx happrox hs (le_max_left _ _)
  have hp1 := pair_approx happrox hs1 (le_max_right _ _)
  set S := ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s u
  set S1 := ∑ u ∈ sqZeros T, (mult T u : ℝ) * Phi s1 u
  have hF : 0 ≤ S - κ * S1 := by
    have : S - κ * S1 = ∑ u ∈ sqZeros T, (mult T u : ℝ) * (Phi s u - κ * Phi s1 u) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    rw [this]
    refine Finset.sum_nonneg fun u hu => ?_
    have := xiF_zero_re (hzero u hu)
    have := Phi_stechkin hs hss him h32 this.1 this.2
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have a := (abs_le.1 hp).2
  have b := (abs_le.1 hp1).1
  have hκε : 2 * ε' + κ * (2 * ε') = ε := by rw [hε']; field_simp
  have hk := mul_nonneg hκ0 (by linarith : 0 ≤ S1 + 2 * ε' - 2 * (logDeriv xiF s1).re)
  nlinarith

end TernaryGoldbach.RSBounds.RS75StechkinCore
