import RSBounds.QuadraticKernelScaling
import RSBounds.QuadraticLowerKernel

/-!
# Bounds for the actual twofold smoothing coefficients

The same near and far coefficients work for the upper and lower averages.
This module makes no zero-count or zero-free assumption; the real-part and
nonreal hypotheses on the argument are explicit.
-/

open Complex

namespace TernaryGoldbach.RSBounds.QuadraticCoefficientBounds

open PolynomialZeroKernel QuadraticZeroKernel QuadraticKernelScaling

theorem abs_im_pow_le_norm_rising_two (ρ : ℂ) :
    |ρ.im| ^ 3 ≤ ‖rising ρ 2‖ := by
  have hn (n : ℕ) : |ρ.im| ≤ ‖ρ + n‖ := by
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      Complex.abs_im_le_norm (ρ + n)
  have h0 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  norm_num [rising, norm_mul]
  calc
    |ρ.im| ^ 3 = |ρ.im| * |ρ.im| * |ρ.im| := by ring
    _ ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ := by
      gcongr
      · simpa using hn 1
      · simpa using hn 2

private theorem low_denominator_le {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (him : ρ.im ≠ 0) :
    (1 + δ) / ‖ρ‖ ≤ (1 + δ) / |ρ.im| :=
  div_le_div_of_nonneg_left (by linarith) (abs_pos.mpr him)
    (Complex.abs_im_le_norm ρ)

private theorem high_denominator_le {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (him : ρ.im ≠ 0) :
    R2 δ / (δ ^ 2 * ‖rising ρ 2‖) ≤ R2 δ / (δ ^ 2 * |ρ.im| ^ 3) := by
  apply div_le_div_of_nonneg_left (by unfold R2; positivity)
    (mul_pos (pow_pos hδ 2) (pow_pos (abs_pos.mpr him) 3))
  exact mul_le_mul_of_nonneg_left (abs_im_pow_le_norm_rising_two ρ) (by positivity)

/-- Near-zero bound for the actual upper average, with the factor `1+delta`. -/
theorem norm_zeroCoefficient_upper_le_low {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    {ρ : ℂ} (hr : 0 < ρ.re) (hr1 : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient x (δ * x) ρ‖ ≤ (1 + δ) * x ^ ρ.re / |ρ.im| := by
  rw [zeroCoefficient_upper hx hδ, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((QuadraticZeroKernel.norm_upperKernel_le_low hδ hr hr1).trans (low_denominator_le hδ him))
    (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

/-- The same near-zero bound for the lower average. -/
theorem norm_zeroCoefficient_lower_le_low {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ2 : 2 * δ < 1) {ρ : ℂ} (hr : 0 < ρ.re) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
      (1 + δ) * x ^ ρ.re / |ρ.im| := by
  rw [zeroCoefficient_lower hx hδ hδ2, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((QuadraticLowerKernel.norm_lower_difference_le_low_common hδ hδ2 hr).trans
      (low_denominator_le hδ him)) (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

/-- Far-zero bound for the actual upper average. -/
theorem norm_zeroCoefficient_upper_le_high {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    {ρ : ℂ} (hr : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient x (δ * x) ρ‖ ≤
      (R2 δ / δ ^ 2) * x ^ ρ.re / |ρ.im| ^ 3 := by
  rw [zeroCoefficient_upper hx hδ, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((QuadraticZeroKernel.norm_upperKernel_le_high hδ hr).trans (high_denominator_le hδ him))
    (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

/-- The same far-zero bound for the lower average. -/
theorem norm_zeroCoefficient_lower_le_high {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ2 : 2 * δ < 1) {ρ : ℂ} (hr : 0 ≤ ρ.re) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
      (R2 δ / δ ^ 2) * x ^ ρ.re / |ρ.im| ^ 3 := by
  rw [zeroCoefficient_lower hx hδ hδ2, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((QuadraticLowerKernel.norm_lower_difference_le_high_common hδ hδ2 hr).trans
      (high_denominator_le hδ him)) (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

end TernaryGoldbach.RSBounds.QuadraticCoefficientBounds
