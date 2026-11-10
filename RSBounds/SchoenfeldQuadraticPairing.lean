import RSBounds.SchoenfeldCoefficientPairing
import RSBounds.QuadraticCoefficientBounds
import RSBounds.SchoenfeldZeroWeights
import RSBounds.SchoenfeldSquareCutoffs

/-!
# Reflection bounds for the actual quadratic smoothing coefficients

The all-zero critical-line allowance uses the far coefficient (T1=0), as
in Schoenfeld's Theorem 11. The high-zero allowance switches from the near
coefficient to the far coefficient at the supplied positive height U.
-/

open Complex Finset Real

namespace TernaryGoldbach.RSBounds.SchoenfeldQuadraticPairing

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open SchoenfeldCoefficientPairing QuadraticZeroKernel QuadraticKernelScaling

noncomputable def criticalCoefficient (δ t : ℝ) : ℝ := (R2 δ / δ ^ 2) / t ^ 3

noncomputable def highCoefficient (δ U t : ℝ) : ℝ :=
  if t ≤ U then (1 + δ) / t else criticalCoefficient δ t

theorem criticalCoefficient_nonneg (δ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ criticalCoefficient δ t := by
  unfold criticalCoefficient R2
  positivity

theorem highCoefficient_nonneg {δ : ℝ} (hδ : 0 < δ) (U : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ highCoefficient δ U t := by
  unfold highCoefficient
  split_ifs
  · positivity
  · exact criticalCoefficient_nonneg δ ht

/-- Rosser's all-zero square allowance gives the cube allowance used at T1=0. -/
theorem rectangle_reciprocal_cube_sum_lt {T : ℝ} (hT : 0 < T) :
    (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 3) <
      0.0463 / 14.13 := by
  have hp : (∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 3) ≤
      (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / ρ.im ^ 2) / 14.13 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hi := RS75XiIncrement.xi_zero_height_lower hz
    have hn := xiF_zero_im_ne_zero hz
    rw [div_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (mul_pos (sq_pos_of_ne_zero hn) (by norm_num : (0 : ℝ) < 14.13))
    calc
      ρ.im ^ 2 * 14.13 = |ρ.im| ^ 2 * 14.13 := by rw [sq_abs]
      _ ≤ |ρ.im| ^ 2 * |ρ.im| := mul_le_mul_of_nonneg_left hi.le (sq_nonneg _)
      _ = |ρ.im| ^ 3 := by ring
  exact hp.trans_lt (div_lt_div_of_pos_right
    (SchoenfeldReciprocalSquare.rectangle_reciprocal_square_sum_lt hT)
    (by norm_num : (0 : ℝ) < 14.13))

/-- The critical-line allowance is the actual reciprocal-cube sum. -/
theorem critical_sum_eq (T x δ : ℝ) :
    (∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) =
      (R2 δ / δ ^ 2) * Real.sqrt x *
        ∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 3 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  unfold criticalCoefficient
  ring

/-- The high allowance splits into the exact Phi0 and Phi2 weighted counts. -/
theorem high_weightedSum_eq {A U T : ℝ} (hU : 0 < U) (hAU : A ≤ U) (hUT : U ≤ T)
    (x δ : ℝ) :
    WeightedZetaZeros.weightedSum A T (fun t => highCoefficient δ U t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) =
      x * ((1 + δ) * WeightedZetaZeros.weightedSum A U
        (SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 0) +
        (R2 δ / δ ^ 2) * WeightedZetaZeros.weightedSum U T
          (SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 2)) := by
  have he : (fun t => highCoefficient δ U t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) =
      (fun t => if t ≤ U then (x * (1 + δ)) *
        SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 0 t
      else (x * (R2 δ / δ ^ 2)) *
        SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 2 t) := by
    funext t
    unfold highCoefficient criticalCoefficient SchoenfeldZeroWeights.Phi
    split_ifs <;> norm_num only [Nat.reduceAdd, pow_one] <;> ring
  rw [he, weightedSum_split_ite hU hAU hUT,
    weightedSum_const_mul, weightedSum_const_mul]
  ring

/-- The actual upper coefficients, with one positive-height high allowance. -/
theorem norm_upper_sum_le
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) (U : ℝ) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => highCoefficient δ U t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hx0 : 0 < x := by linarith
  apply norm_sum_le_critical_and_weighted_high hRH hT hg hx
    (fun ρ => zeroCoefficient x (δ * x) ρ)
    (criticalCoefficient δ) (highCoefficient δ U)
    (fun t ht => criticalCoefficient_nonneg δ ht)
    (fun t ht => highCoefficient_nonneg hδ U ht)
  · intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_upper_le_high hx0 hδ hs.2.le hi
    convert hh using 1 <;> unfold criticalCoefficient <;> ring
  · intro ρ hρ _
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    unfold highCoefficient
    split_ifs
    · have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_upper_le_low hx0 hδ hs.1 hs.2.le hi
      convert hh using 1 <;> ring
    · have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_upper_le_high hx0 hδ hs.2.le hi
      convert hh using 1 <;> unfold criticalCoefficient <;> ring

/-- The actual lower coefficients use the identical positive-height allowance. -/
theorem norm_lower_sum_le
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1) (U : ℝ) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => highCoefficient δ U t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hx0 : 0 < x := by linarith
  apply norm_sum_le_critical_and_weighted_high hRH hT hg hx
    (fun ρ => zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ)
    (criticalCoefficient δ) (highCoefficient δ U)
    (fun t ht => criticalCoefficient_nonneg δ ht)
    (fun t ht => highCoefficient_nonneg hδ U ht)
  · intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_lower_le_high hx0 hδ hδ2 hs.1.le hi
    convert hh using 1 <;> unfold criticalCoefficient <;> ring
  · intro ρ hρ _
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    unfold highCoefficient
    split_ifs
    · have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_lower_le_low hx0 hδ hδ2 hs.1 hi
      convert hh using 1 <;> ring
    · have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_lower_le_high hx0 hδ hδ2 hs.1.le hi
      convert hh using 1 <;> unfold criticalCoefficient <;> ring

end TernaryGoldbach.RSBounds.SchoenfeldQuadraticPairing
