import RSBounds.SchoenfeldQuadraticPairing
import RSBounds.SchoenfeldWeightedZeros

/-!
# A uniform finite-height envelope for Schoenfeld's quadratic zero sum

This binds the actual second-difference coefficients to the exact elementary
Laplace bounds. The upper contour height disappears from the majorant. No
zero-sum estimate is assumed: only the stated finite RH check remains.
-/

open Complex Finset Real

namespace TernaryGoldbach.RSBounds.SchoenfeldQuadraticEnvelope

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open QuadraticZeroKernel QuadraticKernelScaling SchoenfeldQuadraticPairing
open SchoenfeldZeroWeights SchoenfeldLaplaceTails SchoenfeldWeightedZeros

noncomputable def nearAllowance (a U : ℝ) : ℝ :=
  nearPrimitive a d (Real.log (U / 17)) / (2 * Real.pi) +
    2 * rosserR 1.588 U * Phi a 0 U

noncomputable def farAllowance (a U : ℝ) : ℝ :=
  (1 / (2 * Real.pi) + q U) * farPrimitive a d 2 (Real.log (U / 17)) / 289 +
    2 * rosserR 1.588 U * Phi a 2 U

noncomputable def envelope (x δ U : ℝ) : ℝ :=
  (R2 δ / δ ^ 2) * Real.sqrt x * (0.0463 / 14.13) +
    x * ((1 + δ) * nearAllowance (Real.log x / 9.645908801) U +
      (R2 δ / δ ^ 2) * farAllowance (Real.log x / 9.645908801) U)

/-- Both exact weighted-count envelopes are independent of the upper height. -/
theorem norm_le_envelope_of_pairing {T x δ U : ℝ} (hT : 0 < T)
    (hx : 1 < x) (hδ : 0 < δ) (hAU : 1894438.5122 ≤ U) (hUT : U ≤ T)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2)
    {z : ℂ}
    (hz : ‖z‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => highCoefficient δ U t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17))))) :
    ‖z‖ ≤ envelope x δ U := by
  have hx0 : 0 < x := by linarith
  have hU17 : 17 < U := by linarith
  have hU0 : 0 < U := by linarith
  have ha : 0 < Real.log x / 9.645908801 := div_pos (Real.log_pos hx) (by norm_num)
  have hc : 0 ≤ R2 δ / δ ^ 2 := by unfold R2; positivity
  rw [critical_sum_eq, high_weightedSum_eq hU0 hAU hUT] at hz
  have hlo := mul_le_mul_of_nonneg_left (rectangle_reciprocal_cube_sum_lt hT).le
    (mul_nonneg hc (Real.sqrt_nonneg x))
  have hn := near_sum_le ha (by norm_num : (17 : ℝ) < 1894438.5122) hAU hnear
  have hf := far_sum_le ha.le hU17 hUT hfar
  change WeightedZetaZeros.weightedSum 1894438.5122 U
    (Phi (Real.log x / 9.645908801) 0) ≤ nearAllowance (Real.log x / 9.645908801) U at hn
  change WeightedZetaZeros.weightedSum U T
    (Phi (Real.log x / 9.645908801) 2) ≤ farAllowance (Real.log x / 9.645908801) U at hf
  have hn' := mul_le_mul_of_nonneg_left hn (by linarith : 0 ≤ 1 + δ)
  have hf' := mul_le_mul_of_nonneg_left hf hc
  have hhi := mul_le_mul_of_nonneg_left (add_le_add hn' hf') hx0.le
  exact hz.trans (add_le_add hlo hhi)

/-- The actual upper zero sum satisfies the uniform envelope. -/
theorem norm_upper_sum_le_envelope
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ U : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 < x) (hδ : 0 < δ)
    (hAU : 1894438.5122 ≤ U) (hUT : U ≤ T)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ ≤ envelope x δ U :=
  norm_le_envelope_of_pairing hT hx hδ hAU hUT hnear hfar
    (norm_upper_sum_le hRH hT hg hx.le hδ U)

/-- The actual lower zero sum satisfies the same uniform envelope. -/
theorem norm_lower_sum_le_envelope
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ U : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    (hAU : 1894438.5122 ≤ U) (hUT : U ≤ T)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
        envelope x δ U :=
  norm_le_envelope_of_pairing hT hx hδ hAU hUT hnear hfar
    (norm_lower_sum_le hRH hT hg hx.le hδ hδ2 U)

end TernaryGoldbach.RSBounds.SchoenfeldQuadraticEnvelope
