import RSBounds.PolynomialLowerKernel

/-!
# Actual second-difference zero coefficients

The integration identities and affine integral bound are reused from
`PolynomialZeroKernel` at n=2. The high coefficient retains the exact
polynomial R₂(δ)=((1+δ)^3+1)^2. No zero-location hypothesis is used beyond
explicit inequalities on the supplied complex argument.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace TernaryGoldbach.RSBounds.QuadraticZeroKernel

open PolynomialZeroKernel

theorem forwardDiff_two (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    forwardDiff h 2 f x = f (x + 2 * h) - 2 * f (x + h) + f x := by
  simp only [forwardDiff]
  rw [show x + h + h = x + 2 * h by ring]
  ring

/-- The repeated integral is exactly the finite difference of the second antiderivative. -/
theorem zero_term_twofold_identity {ρ : ℂ} (hρ : 0 < ρ.re)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    iteratedIntegral h 2 (fun t => (t : ℂ) ^ ρ / ρ) x =
      forwardDiff h 2 (antiderivative ρ 2) x := by
  have hz : antiderivative ρ 0 = fun t : ℝ => (t : ℂ) ^ ρ / ρ := by
    funext t
    simp [antiderivative, rising]
  have hc : ∀ x, 0 < x → ContinuousAt (antiderivative ρ 0) x := by
    intro x hx
    have hr : ρ ≠ 0 := by simpa using add_nat_ne_zero hρ 0
    rw [hz]
    exact ((hasDerivAt_ofReal_cpow_const hx.ne' hr).div_const ρ).continuousAt
  simpa only [hz] using
    iteratedIntegral_eq_forwardDiff hh (antiderivative ρ)
      (fun n x hx => antiderivative_hasDerivAt hρ n hx) hc 2 x hx

/-- The low-zero estimate, before dividing by the smoothing volume `h^2`. -/
theorem norm_second_difference_le_low {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖forwardDiff h 2 (antiderivative ρ 2) x‖ ≤
      h ^ 2 * (x ^ ρ.re / ‖ρ‖) * (1 + h / x) := by
  rw [← zero_term_twofold_identity hρ hx hh]
  have hf : ∀ t, x ≤ t → ‖(t : ℂ) ^ ρ / ρ‖ ≤ 0 + (x ^ ρ.re / (x * ‖ρ‖)) * t := by
    intro t ht
    simpa only [zero_add] using norm_zero_term_le_affine hρ hρ1 hx ht
  have hm := norm_iteratedIntegral_le_affine hh (fun t => (t : ℂ) ^ ρ / ρ)
    0 (x ^ ρ.re / (x * ‖ρ‖)) 2 x hf
  have hn : ρ ≠ 0 := by simpa using add_nat_ne_zero hρ 0
  have hn0 : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  refine hm.trans_eq ?_
  norm_num
  field_simp [hx.ne', hn0]

theorem norm_normalized_second_difference_le_low {ρ : ℂ}
    (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖forwardDiff h 2 (antiderivative ρ 2) x / (h : ℂ) ^ 2‖ ≤
      (x ^ ρ.re / ‖ρ‖) * (1 + h / x) := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
    div_le_iff₀ (pow_pos hh 2)]
  have hm := norm_second_difference_le_low hρ hρ1 hx hh.le
  nlinarith

/-- The dimensionless second-difference numerator. -/
noncomputable def numerator (δ : ℝ) (ρ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 3,
    (-1 : ℂ) ^ j * (Nat.choose 2 j : ℂ) * ((1 + (j : ℝ) * δ : ℝ) : ℂ) ^ (ρ + 2)

/-- The normalized zero coefficient for the upper twofold average. -/
noncomputable def upperKernel (δ : ℝ) (ρ : ℂ) : ℂ :=
  numerator δ ρ / ((δ : ℂ) ^ 2 * rising ρ 2)

def R2 (δ : ℝ) : ℝ := ((1 + δ) ^ 3 + 1) ^ 2

theorem upperKernel_eq_normalized_difference (δ : ℝ) (ρ : ℂ) :
    upperKernel δ ρ = forwardDiff δ 2 (antiderivative ρ 2) 1 / (δ : ℂ) ^ 2 := by
  simp only [upperKernel, numerator, forwardDiff_two, antiderivative]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- The exact low-zero factor for m=2. -/
theorem norm_upperKernel_le_low {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) :
    ‖upperKernel δ ρ‖ ≤ (1 + δ) / ‖ρ‖ := by
  rw [upperKernel_eq_normalized_difference]
  have hm := norm_normalized_second_difference_le_low hρ hρ1 (by norm_num : (0 : ℝ) < 1) hδ
  simpa only [Real.one_rpow, one_div, div_one, inv_one, one_mul, mul_one, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hm

theorem norm_numerator_le_R2 {δ : ℝ} (hδ : 0 ≤ δ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    ‖numerator δ ρ‖ ≤ R2 δ := by
  have hterm (j : ℕ) :
      ‖(-1 : ℂ) ^ j * (Nat.choose 2 j : ℂ) *
          ((1 + (j : ℝ) * δ : ℝ) : ℂ) ^ (ρ + 2)‖ ≤
        (Nat.choose 2 j : ℝ) * (((1 + δ) ^ 3) ^ j) := by
    have hb : 1 ≤ 1 + (j : ℝ) * δ := by
      linarith [mul_nonneg (Nat.cast_nonneg j) hδ]
    have hb0 : 0 < 1 + (j : ℝ) * δ := by linarith
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      Complex.norm_natCast, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb0]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hp : (1 + (j : ℝ) * δ) ^ (ρ + 2).re ≤ (1 + (j : ℝ) * δ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb (by simpa using (show ρ.re + 2 ≤ 3 by linarith))
    rw [Real.rpow_ofNat] at hp
    have hber : 1 + (j : ℝ) * δ ≤ (1 + δ) ^ j :=
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ δ) j
    calc (1 + (j : ℝ) * δ) ^ (ρ + 2).re ≤ (1 + (j : ℝ) * δ) ^ 3 := hp
      _ ≤ ((1 + δ) ^ j) ^ 3 := pow_le_pow_left₀ hb0.le hber 3
      _ = ((1 + δ) ^ 3) ^ j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  unfold numerator
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq ?_)
  set z := (1 + δ) ^ 3
  change (∑ j ∈ Finset.range 3, (Nat.choose 2 j : ℝ) * z ^ j) = (z + 1) ^ 2
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- The high-zero estimate with its exact quadratic-smoothing numerator bound. -/
theorem norm_upperKernel_le_high {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    ‖upperKernel δ ρ‖ ≤ R2 δ / (δ ^ 2 * ‖rising ρ 2‖) := by
  unfold upperKernel
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  exact div_le_div_of_nonneg_right (norm_numerator_le_R2 hδ.le hρ) (by positivity)



end TernaryGoldbach.RSBounds.QuadraticZeroKernel
