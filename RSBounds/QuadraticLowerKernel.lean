import RSBounds.QuadraticZeroKernel

/-! Lower-average bounds for the twofold additive smoothing coefficient.
The generic bounded-integral and finite-difference inequalities are reused.
-/

open Complex MeasureTheory Set
open TernaryGoldbach.RSBounds.PolynomialZeroKernel
open TernaryGoldbach.RSBounds.PolynomialZeroCancellation
open TernaryGoldbach.RSBounds.PolynomialLowerKernel
open TernaryGoldbach.RSBounds.QuadraticZeroKernel

namespace TernaryGoldbach.RSBounds.QuadraticLowerKernel

/-- The lower average has low-zero coefficient at most `1/|rho|`. -/
theorem norm_lower_difference_le_low {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2‖ ≤ 1 / ‖ρ‖ := by
  have hx : 0 < 1 - 2 * δ := by linarith
  rw [← zero_term_twofold_identity hρ hx hδ.le]
  have hm := norm_iteratedIntegral_le_const_on hδ.le
    (fun t : ℝ => (t : ℂ) ^ ρ / ρ) (1 / ‖ρ‖) 2 (1 - 2 * δ) (by
      intro t ht
      have ht0 : 0 < t := hx.trans_le ht.1
      have ht1 : t ≤ 1 := by norm_num at ht; linarith [ht.2]
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      exact div_le_div_of_nonneg_right (Real.rpow_le_one ht0.le ht1 hρ.le) (norm_nonneg _))
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  apply (div_le_iff₀ (pow_pos hδ 2)).mpr
  convert hm using 1 <;> ring

/-- The lower finite-difference numerator has coefficient sum `4`. -/
theorem norm_lower_difference_le_high {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2‖ ≤
      4 / (δ ^ 2 * ‖rising ρ 2‖) := by
  have hx : 0 < 1 - 2 * δ := by linarith
  have hm := norm_forwardDiff_le_const_on hδ.le (antiderivative ρ 2)
    (1 / ‖rising ρ 2‖) 2 (1 - 2 * δ) (by
      intro t ht
      have ht0 : 0 < t := hx.trans_le ht.1
      have ht1 : t ≤ 1 := by norm_num at ht; linarith [ht.2]
      rw [antiderivative, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      apply Real.rpow_le_one ht0.le ht1
      simpa using (show 0 ≤ ρ.re + 2 by linarith))
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ)‖ / δ ^ 2 ≤
      (2 ^ 2 * (1 / ‖rising ρ 2‖)) / δ ^ 2 := by gcongr
    _ = 4 / (δ ^ 2 * ‖rising ρ 2‖) := by ring

theorem four_le_R2 {δ : ℝ} (hδ : 0 ≤ δ) : 4 ≤ R2 δ := by
  have h1 : (1 : ℝ) ≤ (1 + δ) ^ 3 := one_le_pow₀ (by linarith)
  have h2 : (2 : ℝ) ^ 2 ≤ ((1 + δ) ^ 3 + 1) ^ 2 := by gcongr; linarith
  norm_num [R2] at h2 ⊢
  exact h2

/-- The same `R2` high-zero majorant can therefore be used for both signs. -/
theorem norm_lower_difference_le_high_common {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2‖ ≤
      R2 δ / (δ ^ 2 * ‖rising ρ 2‖) :=
  (norm_lower_difference_le_high hδ hδ2 hρ).trans
    (div_le_div_of_nonneg_right (four_le_R2 hδ.le) (by positivity))

/-- The upper low-zero factor `1+delta` also majorizes the lower average. -/
theorem norm_lower_difference_le_low_common {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2‖ ≤
      (1 + δ) / ‖ρ‖ :=
  (norm_lower_difference_le_low hδ hδ2 hρ).trans
    (div_le_div_of_nonneg_right (by linarith) (norm_nonneg _))

end TernaryGoldbach.RSBounds.QuadraticLowerKernel
