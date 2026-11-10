import RSBounds.QuadraticKernel
import RSBounds.QuadraticSubOne
import RSBounds.PolynomialZetaFormula
import RSBounds.PolynomialPrimeSum
import RSBounds.QuadraticPsiMellin
import TernaryGoldbach.Explicit.ZetaExplicit
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# A quadratic explicit formula with an explicit left remainder

The rational Mellin kernel is used off its half-plane of convergence. The
prime-sum identity uses only its equality with the Mellin integral on the
right line. The pole at zero contributes `log(2π)/2`.

The left vertical integral is retained, not identified with the trivial-zero
sum. This is a twofold integrated formula, not a numerical bound for psi.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.QuadraticZeta

open TernaryGoldbach.Explicit PolynomialExplicit QuadraticKernel QuadraticMellin
  QuadraticContourLimit QuadraticSubOne

theorem prime_sum_eq_right_line {x : ℝ} (hx : 0 < x) :
    SsumG (1 : DirichletCharacter ℂ 1) weight x =
      -(1 / (2 * π) : ℂ) *
        ∫ t : ℝ, contourIntegrand riemannZeta kernel x (((3 / 2 : ℝ) : ℂ) + t * I) := by
  have hline : (fun t : ℝ => mellin weight (((3 / 2 : ℝ) : ℂ) + t * I)) =
      fun t : ℝ => kernel (((3 / 2 : ℝ) : ℂ) + t * I) := by
    funext t
    exact mellin_weight (by simp)
  have hc : Continuous (fun t : ℝ => mellin weight (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [hline]
    exact decayTwo_kernel.continuous_line _ (Or.inr rfl)
  have hi : Integrable (fun t : ℝ => mellin weight (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [hline]
    exact decayTwo_kernel.integrable_line (Or.inr rfl)
  have hS := PolynomialPrimeSum.SsumG_eq_line (1 : DirichletCharacter ℂ 1)
    (fun _ _ => continuous_weight.continuousAt)
    (mellinConvergent_weight (by norm_num)) hc hi hx
  have hF (t : ℝ) : Fline (1 : DirichletCharacter ℂ 1) weight x
      (((3 / 2 : ℝ) : ℂ) + t * I) =
      -contourIntegrand riemannZeta kernel x (((3 / 2 : ℝ) : ℂ) + t * I) := by
    rw [Fline, contourIntegrand, LFunction_one_mod_one, logDeriv_apply,
      mellin_weight (by simp)]
    ring
  simpa only [hF, integral_neg, mul_neg, neg_mul] using hS

private theorem contourIntegrand_zetaF_eq (x : ℝ) {s : ℂ}
    (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    contourIntegrand zetaF kernel x s =
      contourIntegrand (fun z : ℂ => z - 1) kernel x s +
        contourIntegrand riemannZeta kernel x s := by
  rw [contourIntegrand, contourIntegrand, contourIntegrand,
    logDeriv_zetaF_eq hs hz, logDeriv_sub_one]
  ring

/-- The ordinary quadratic Mellin kernel gives a zero-sum formula with the
constant at zero evaluated and the left vertical remainder retained. -/
theorem explicit_formula_zeta_quadratic_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        (kernel u * (x : ℂ) ^ u)) atTop
        (𝓝 ((x : ℂ) / 6 - SsumG (1 : DirichletCharacter ℂ 1) weight x -
          (1 / (2 * π) : ℂ) *
            (∫ y : ℝ, contourIntegrand riemannZeta kernel x
              (((-1 / 2 : ℝ) : ℂ) + y * I)) - Complex.log (2 * π) / 2)) := by
  have hz0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hlim := explicit_formula_zetaF_at_heights hx hT
  have hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ numerator s :=
    fun _ hs => differentiableAt_numerator hs
  have hM : DecayTwo (fun s => numerator s / s) 27 := by
    simpa only [← kernel_eq_numerator_div] using decayTwo_kernel
  have hmain := sub_one_contour_difference hH hM hx
  simp only [← kernel_eq_numerator_div, numerator_one, numerator_zero] at hmain
  have hR1 : ∀ y : ℝ, ((3 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  have hL1 : ∀ y : ℝ, ((-1 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  have hRz : ∀ y : ℝ, riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
  have hLz : ∀ y : ℝ, riemannZeta (((-1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    zeta_ne_zero_of_zetaF (hL1 y)
      (zetaF_ne_zero_strip (by simp; norm_num) (by simp; norm_num))
  have iR := QuadraticContourLimit.integrable_contour_right ldatum_zeta2 decayTwo_kernel hx
  have iL := integrable_zetaF_contour_left decayTwo_kernel hx
  have iR1 := QuadraticContourLimit.integrable_contour_right ldatum_sub_one decayTwo_kernel hx
  have iL1 := integrable_sub_one_contour_left decayTwo_kernel hx
  set A := ∫ y : ℝ, contourIntegrand zetaF kernel x (((3 / 2 : ℝ) : ℂ) + y * I) with hA
  set A1 := ∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) kernel x
    (((3 / 2 : ℝ) : ℂ) + y * I) with hA1
  set Bv := ∫ y : ℝ, contourIntegrand zetaF kernel x (((-1 / 2 : ℝ) : ℂ) + y * I) with hBv
  set B1v := ∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) kernel x
    (((-1 / 2 : ℝ) : ℂ) + y * I) with hB1v
  have IR : ∫ y : ℝ, contourIntegrand riemannZeta kernel x
      (((3 / 2 : ℝ) : ℂ) + y * I) = A - A1 := by
    rw [hA, hA1, ← integral_sub iR iR1]
    congr 1
    ext y
    rw [contourIntegrand_zetaF_eq x (hR1 y) (hRz y)]
    ring
  have IL : ∫ y : ℝ, contourIntegrand riemannZeta kernel x
      (((-1 / 2 : ℝ) : ℂ) + y * I) = Bv - B1v := by
    rw [hBv, hB1v, ← integral_sub iL iL1]
    congr 1
    ext y
    rw [contourIntegrand_zetaF_eq x (hL1 y) (hLz y)]
    ring
  have hS := prime_sum_eq_right_line hx
  rw [IR] at hS
  have hzero : logDeriv zetaF 0 = logDeriv (fun s : ℂ => s - 1) 0 +
      Complex.log (2 * π) := by
    rw [logDeriv_zetaF_eq (by norm_num) hz0, logDeriv_sub_one,
      PolynomialZeta.logDeriv_riemannZeta_zero]
  have hmain' : (x : ℂ) / 6 = (1 / (2 * π) : ℂ) * (A1 - B1v) -
      logDeriv (fun s : ℂ => s - 1) 0 / 2 := by
    calc
      _ = (1 / 6 : ℂ) * (x : ℂ) := by ring
      _ = (1 / (2 * π) : ℂ) * (A1 - B1v) -
          logDeriv (fun s : ℂ => s - 1) 0 * (1 / 2) := hmain
      _ = _ := by ring
  convert hlim using 2
  rw [hmain', hS, IL, hzero]
  ring

/-- Existential form of the quadratic formula for zeta. -/
theorem explicit_formula_zeta_quadratic {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        (kernel u * (x : ℂ) ^ u)) atTop
        (𝓝 ((x : ℂ) / 6 - SsumG (1 : DirichletCharacter ℂ 1) weight x -
          (1 / (2 * π) : ℂ) *
            (∫ y : ℝ, contourIntegrand riemannZeta kernel x
              (((-1 / 2 : ℝ) : ℂ) + y * I)) - Complex.log (2 * π) / 2)) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  exact ⟨T, hT.mem, explicit_formula_zeta_quadratic_at_heights hT hx⟩

/-- The unevaluated left vertical contribution to the second primitive. -/
noncomputable def psi2LeftRemainder (x : ℝ) : ℂ :=
  (x : ℂ) ^ 2 / (2 * π) *
    ∫ y : ℝ, contourIntegrand riemannZeta kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)

/-- The fixed-strip explicit formula written for the actual twofold
primitive `Psi2 x = ∑ Λ(n) (x-n)_+^2/2`. -/
theorem explicit_formula_Psi2_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        ((x : ℂ) ^ (u + 2) / (u * (u + 1) * (u + 2)))) atTop
        (𝓝 ((x : ℂ) ^ 3 / 6 - (QuadraticPsi.Psi2 x : ℂ) - psi2LeftRemainder x -
          (x : ℂ) ^ 2 * Complex.log (2 * π) / 2)) := by
  have hlim := explicit_formula_zeta_quadratic_at_heights hT hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsum (k : ℕ) :
      (x : ℂ) ^ 2 * (∑ u ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) u : ℂ) * (kernel u * (x : ℂ) ^ u)) =
      ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        ((x : ℂ) ^ (u + 2) / (u * (u + 1) * (u + 2))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Complex.cpow_add _ _ hx0, Complex.cpow_ofNat]
    unfold kernel
    ring
  have hscaled := hlim.const_mul ((x : ℂ) ^ 2)
  simp_rw [hsum] at hscaled
  simp only [mul_sub] at hscaled
  rw [QuadraticPsiMellin.pow_two_mul_SsumG_quadratic_eq_Psi2 hx] at hscaled
  convert hscaled using 2 <;> unfold psi2LeftRemainder <;> ring

/-- Existential form of the twofold primitive formula. -/
theorem explicit_formula_Psi2 {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        ((x : ℂ) ^ (u + 2) / (u * (u + 1) * (u + 2)))) atTop
        (𝓝 ((x : ℂ) ^ 3 / 6 - (QuadraticPsi.Psi2 x : ℂ) - psi2LeftRemainder x -
          (x : ℂ) ^ 2 * Complex.log (2 * π) / 2)) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  exact ⟨T, hT.mem, explicit_formula_Psi2_at_heights hT hx⟩

end TernaryGoldbach.RSBounds.QuadraticZeta
