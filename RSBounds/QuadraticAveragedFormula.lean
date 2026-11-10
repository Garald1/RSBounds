/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import RSBounds.QuadraticZetaFormula
import RSBounds.QuadraticKernelScaling

/-!
# Assembling the twofold averaged explicit formula

All three primitive formulas use one sequence of good contour heights. Their
second finite difference gives the upper polynomial smoothing of psi, with
main term `x + h`, constant `-log(2*pi)`, and an explicit left remainder.
No estimate for the zero sum or remainder is assumed or asserted here.
-/

open Complex Finset Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.QuadraticAveraged

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialZeroKernel
open QuadraticZeta QuadraticPsi QuadraticZeroKernel QuadraticKernelScaling

/-- The left contour remainder after the same averaging operation. -/
noncomputable def leftRemainder (x h : ℝ) : ℂ :=
  forwardDiff h 2 psi2LeftRemainder x / (h : ℂ) ^ 2

private theorem antiderivative_two_eq (ρ : ℂ) (x : ℝ) :
    antiderivative ρ 2 x =
      (x : ℂ) ^ (ρ + 2) / (ρ * (ρ + 1) * (ρ + 2)) := by
  norm_num [antiderivative, rising]

private theorem forwardDiff_two_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 2 (fun t => ∑ i ∈ s, f i t) x =
      ∑ i ∈ s, forwardDiff h 2 (f i) x := by
  simp only [forwardDiff_two, sum_add_distrib, sum_sub_distrib, mul_sum]

private theorem forwardDiff_two_mul (c : ℂ) (f : ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 2 (fun t => c * f t) x = c * forwardDiff h 2 f x := by
  simp only [forwardDiff_two]
  ring

private theorem forwardDiff_two_sub (f g : ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 2 (fun t => f t - g t) x =
      forwardDiff h 2 f x - forwardDiff h 2 g x := by
  simp only [forwardDiff_two]
  ring

/-- The finite difference of the integrated main term. -/
theorem normalized_main_term {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    forwardDiff h 2 (fun t : ℝ => (t : ℂ) ^ 3 / 6) x / (h : ℂ) ^ 2 =
      ((x + h : ℝ) : ℂ) := by
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  rw [forwardDiff_two]
  push_cast
  field_simp [hh0]
  ring

/-- Twofold averaging leaves the constant at the zero pole unchanged. -/
theorem normalized_zero_pole {h : ℝ} (hh : h ≠ 0) (x : ℝ) (c : ℂ) :
    forwardDiff h 2 (fun t : ℝ => (t : ℂ) ^ 2 * c / 2) x / (h : ℂ) ^ 2 = c := by
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  rw [forwardDiff_two]
  push_cast
  field_simp [hh0]
  ring

/-- Casting the finite arithmetic smoothing identity into the complex formula. -/
theorem normalized_Psi2 {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    forwardDiff h 2 (fun t => (Psi2 t : ℂ)) x / (h : ℂ) ^ 2 =
      (psiUpper N x h : ℂ) := by
  have hc := congrArg (fun t : ℝ => (t : ℂ))
    (secondDifference_Psi2 hx hh hN)
  simpa only [forwardDiff_two, secondDifference, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat] using hc

private theorem tendsto_normalized_forwardDiff_two
    {F : ℕ → ℝ → ℂ} {G : ℝ → ℂ} (x h : ℝ)
    (h0 : Tendsto (fun k => F k x) atTop (𝓝 (G x)))
    (h1 : Tendsto (fun k => F k (x + h)) atTop (𝓝 (G (x + h))))
    (h2 : Tendsto (fun k => F k (x + 2 * h)) atTop (𝓝 (G (x + 2 * h)))) :
    Tendsto (fun k => forwardDiff h 2 (F k) x / (h : ℂ) ^ 2) atTop
      (𝓝 (forwardDiff h 2 G x / (h : ℂ) ^ 2)) := by
  simpa only [forwardDiff_two] using
    ((h2.sub (h1.const_mul 2)).add h0).div_const ((h : ℂ) ^ 2)

/-- The upper twofold averaged explicit formula along a common sequence
of good heights. The left contour remainder is retained explicitly. -/
theorem explicit_formula_upper_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ) atTop
      (𝓝 (((x + h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
        leftRemainder x h - Complex.log (2 * Real.pi))) := by
  let F : ℕ → ℝ → ℂ := fun k t => ∑ ρ ∈ zerosRectD zetaF (T k),
    (multRectD zetaF (T k) ρ : ℂ) * antiderivative ρ 2 t
  let G : ℝ → ℂ := fun t => (t : ℂ) ^ 3 / 6 - (Psi2 t : ℂ) -
    psi2LeftRemainder t - (t : ℂ) ^ 2 * Complex.log (2 * Real.pi) / 2
  have hlim (t : ℝ) (ht : 0 < t) : Tendsto (fun k => F k t) atTop (𝓝 (G t)) := by
    simpa only [F, G, antiderivative_two_eq] using
      explicit_formula_Psi2_at_heights hT ht
  have havg := tendsto_normalized_forwardDiff_two x h (hlim x hx)
    (hlim (x + h) (by linarith)) (hlim (x + 2 * h) (by linarith))
  have hsum (k : ℕ) : forwardDiff h 2 (F k) x / (h : ℂ) ^ 2 =
      ∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ := by
    dsimp only [F]
    rw [forwardDiff_two_sum, sum_div]
    apply sum_congr rfl
    intro ρ _
    rw [forwardDiff_two_mul, mul_div_assoc]
    rfl
  have hvalue : forwardDiff h 2 G x / (h : ℂ) ^ 2 =
      ((x + h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
        leftRemainder x h - Complex.log (2 * Real.pi) := by
    dsimp only [G]
    rw [forwardDiff_two_sub, forwardDiff_two_sub, forwardDiff_two_sub,
      sub_div, sub_div, sub_div, normalized_main_term hh.ne',
      normalized_Psi2 hx.le hh hN, normalized_zero_pole hh.ne']
    rfl
  simpa only [hsum, hvalue] using havg

/-- Existence form of the upper averaged formula; no zero-location premise. -/
theorem explicit_formula_upper {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ) atTop
        (𝓝 (((x + h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
          leftRemainder x h - Complex.log (2 * Real.pi))) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  exact ⟨T, hT.mem, explicit_formula_upper_at_heights hT hx hh hN⟩

/-- The same formula shifted to give the lower polynomial smoothing. -/
theorem explicit_formula_lower_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x h : ℝ} (hx : 2 * h < x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient (x - 2 * h) h ρ) atTop
      (𝓝 (((x - h : ℝ) : ℂ) - (psiLower N x h : ℂ) -
        leftRemainder (x - 2 * h) h - Complex.log (2 * Real.pi))) := by
  have hv := explicit_formula_upper_at_heights hT (x := x - 2 * h)
    (by linarith) hh (show x - 2 * h + 2 * h ≤ N by linarith)
  simpa only [psiUpper, psiLower, sub_add_cancel,
    show x - 2 * h + h = x - h by ring] using hv

end TernaryGoldbach.RSBounds.QuadraticAveraged
