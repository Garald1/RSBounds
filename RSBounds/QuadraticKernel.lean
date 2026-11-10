import RSBounds.QuadraticMellin
import RSBounds.QuadraticContourLimit

/-!
# The twice-integrated kernel in the existing contour theorem

The numerator `1/((s+1)(s+2))` is holomorphic on `Re s>-1`.
Its quotient by `s` satisfies the already established degree-two contour
hypotheses. No new contour argument or zero-location premise is used.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.QuadraticKernel

open TernaryGoldbach.Explicit PolynomialExplicit QuadraticMellin QuadraticContourLimit

noncomputable def numerator (s : ℂ) : ℂ := 1 / ((s + 1) * (s + 2))

theorem kernel_eq_numerator_div (s : ℂ) : kernel s = numerator s / s := by
  simp only [kernel, numerator, div_div]
  congr 1
  ring

theorem numerator_zero : numerator 0 = 1 / 2 := by norm_num [numerator]

theorem numerator_one : numerator 1 = 1 / 6 := by norm_num [numerator]

theorem differentiableAt_numerator {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ numerator s := by
  have hn (n : ℕ) (hn : 1 ≤ n) : s + n ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [add_re, natCast_re, zero_re] at he
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : s + 1 ≠ 0 := by simpa using hn 1 le_rfl
  have h2 : s + 2 ≠ 0 := by simpa using hn 2 (by omega)
  unfold numerator
  exact (differentiableAt_const _).div
    ((differentiableAt_id.add_const 1).mul (differentiableAt_id.add_const 2))
    (mul_ne_zero h1 h2)

private theorem norm_kernel_le {s : ℂ} {d : ℝ} (hd : 0 < d)
    (h0 : d ≤ ‖s‖) (h1 : d ≤ ‖s + 1‖) (h2 : d ≤ ‖s + 2‖) :
    ‖kernel s‖ ≤ 1 / d ^ 3 := by
  have hp : d ^ 3 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by
    calc
      d ^ 3 = d * d * d := by ring
      _ ≤ _ := by gcongr
  simpa only [kernel, norm_div, norm_one, norm_mul] using
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (pow_pos hd 3) hp

private theorem factor_lower (σ t : ℝ) (hσ : σ = -1 / 2 ∨ σ = 3 / 2)
    (n : ℕ) (hn : n ≤ 2) :
    (1 + |t|) / 3 ≤ ‖((σ : ℂ) + t * I) + n‖ := by
  have hreal : (1 / 2 : ℝ) ≤ |σ + n| := by
    rcases hσ with rfl | rfl <;> interval_cases n <;> norm_num
  have hr := Complex.abs_re_le_norm (((σ : ℂ) + t * I) + n)
  have hi := Complex.abs_im_le_norm (((σ : ℂ) + t * I) + n)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, natCast_re] at hr
  simp only [add_im, ofReal_im, ofReal_re, mul_im, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add, natCast_im] at hi
  linarith

theorem norm_kernel_line_le_cube (σ t : ℝ) (hσ : σ = -1 / 2 ∨ σ = 3 / 2) :
    ‖kernel ((σ : ℂ) + t * I)‖ ≤ 27 / (1 + |t|) ^ 3 := by
  have hn (n : ℕ) (hn : n ≤ 2) := factor_lower σ t hσ n hn
  have h := norm_kernel_le (s := (σ : ℂ) + t * I)
    (d := (1 + |t|) / 3) (by positivity)
    (by simpa using hn 0 (by omega))
    (by simpa using hn 1 (by omega))
    (by simpa using hn 2 (by omega))
  refine h.trans_eq ?_
  have hp : 1 + |t| ≠ 0 := by positivity
  field_simp [hp]
  <;> ring

theorem decayTwo_kernel : DecayTwo kernel 27 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro σ hσ
    have hn (n : ℕ) (hn : n ≤ 2) (t : ℝ) :
        ((σ : ℂ) + t * I) + n ≠ 0 := by
      apply norm_pos_iff.mp
      exact lt_of_lt_of_le (by positivity) (factor_lower σ t hσ n hn)
    unfold kernel
    refine continuous_const.div (by fun_prop) (fun t => ?_)
    have h0 : ((σ : ℂ) + t * I) ≠ 0 := by simpa using hn 0 (by omega) t
    have h1 : ((σ : ℂ) + t * I) + 1 ≠ 0 := by simpa using hn 1 (by omega) t
    have h2 : ((σ : ℂ) + t * I) + 2 ≠ 0 := by simpa using hn 2 (by omega) t
    exact mul_ne_zero (mul_ne_zero h0 h1) h2
  · intro σ hσ t
    refine (norm_kernel_line_le_cube σ t hσ).trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h := mul_nonneg (sq_nonneg (1 + |t|)) (abs_nonneg t)
    nlinarith
  · intro s _ _ ht
    have hn (n : ℕ) : |s.im| ≤ ‖s + n‖ := by
      simpa using Complex.abs_im_le_norm (s + n)
    have h := norm_kernel_le (s := s) (d := |s.im|) (by linarith)
      (by simpa using hn 0) (by simpa using hn 1) (by simpa using hn 2)
    refine h.trans ?_
    have hd : 0 < |s.im| := by linarith
    have he : 1 / |s.im| ^ 3 ≤ 1 / |s.im| ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [mul_nonneg (sq_nonneg |s.im|) (show 0 ≤ |s.im| - 1 by linarith)]
    exact he.trans (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _))

/-- The actual-zeta entire-factor formula for the quadratic weight. -/
theorem explicit_formula_zetaF_at_heights {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hT : GoodHeights zetaF BPz2 T) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
      (kernel u * (x : ℂ) ^ u)) atTop
      (𝓝 ((1 / (2 * π) : ℂ) *
        ((∫ y : ℝ, contourIntegrand zetaF kernel x (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, contourIntegrand zetaF kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)) -
        logDeriv zetaF 0 / 2)) := by
  have hM : DecayTwo (fun s => numerator s / s) 27 := by
    simpa only [← kernel_eq_numerator_div] using decayTwo_kernel
  simpa only [← kernel_eq_numerator_div, numerator_zero, mul_one_div] using
    QuadraticContourLimit.explicit_formula_pole_zero_at_heights
      (fun _ hs => differentiableAt_numerator hs) hM hx hT

end TernaryGoldbach.RSBounds.QuadraticKernel
