import RSBounds.HelfgottB6.Sound
import RSBounds.HelfgottB6.GridA
import RSBounds.HelfgottB6.GridBpos
import RSBounds.HelfgottB6.GridBneg

/-!
# [H, Lemma B.1.2, (B.6)] with the book's constant: `|η̂₂''|_∞ ≤ 31.521`

`TernaryGoldbach.MinorArcs.norm_eta2DD_le` (in `calr3/ternary-goldbach`) proves `‖eta2DD t‖ ≤ 32`
for `t ≥ 0`. Here we prove the book's constant `31.521`, for Charlie Reams's own definition
`TernaryGoldbach.MinorArcs.eta2DD` (`eta2DD t = (2πt)² η̂₂(t)` by `eta2DD_eq`):

* `x = 2πt ≤ 28`: Taylor polynomials of degree `< 90` in `x` and a kernel-checked bisection of
  `[0, 28]` (`goodA`; in 16 chunks, each its own kernel-checked declaration in
  `GridA.lean`), as in `Eta2DDTaylor.lean` but with the bound `31.521`;
* `2πt ≥ 28`: ten integrations by parts (`norm_eta2DD_sub_FK`: remainder
  `4 · 10! · (4¹¹ − 1) w¹⁰`, `w = 1/(2πt) ≤ 1/28`) and a kernel-checked second-order bisection of
  `{±1} × [−1, 1] × [0, 1/28]` in `(s, m, w)`, `z = s · zm(m)` (`goodB_pos`, `goodB_neg`; 8 and 64
  chunks in `m`, each its own kernel-checked declaration in `GridBpos.lean`, `GridBneg.lean`).

The true maximum of `‖eta2DD‖` is about `31.52065`, at `t ≈ 17.415` (numerically; not used), so
the margin is about `0.00035`; this is why the second region uses second-order cell bounds.
-/

open Real Complex
open scoped FourierTransform

namespace RSBounds.HelfgottB6

open TernaryGoldbach TernaryGoldbach.MinorArcs
open TernaryGoldbach.Helfgott (eta2)

theorem goodB_pos : GoodB 1 (-1) 1 0 (1 / 28) := by
  have h := GoodB_of_chunks (s := 1) (Or.inl rfl) (-1) (1 / 4) (1 / 28) 7 fun i hi => by
    interval_cases i
    exacts [
      gBpos_00,
      gBpos_01,
      gBpos_02,
      gBpos_03,
      gBpos_04,
      gBpos_05,
      gBpos_06,
      gBpos_07]
  rwa [show (-1 : ℚ) + (((7 : ℕ) : ℚ) + 1) * (1 / 4) = 1 by norm_num] at h

theorem goodB_neg : GoodB (-1) (-1) 1 0 (1 / 28) := by
  have h := GoodB_of_chunks (s := -1) (Or.inr rfl) (-1) (1 / 32) (1 / 28) 63 fun i hi => by
    interval_cases i
    exacts [
      gBneg_00,
      gBneg_01,
      gBneg_02,
      gBneg_03,
      gBneg_04,
      gBneg_05,
      gBneg_06,
      gBneg_07,
      gBneg_08,
      gBneg_09,
      gBneg_10,
      gBneg_11,
      gBneg_12,
      gBneg_13,
      gBneg_14,
      gBneg_15,
      gBneg_16,
      gBneg_17,
      gBneg_18,
      gBneg_19,
      gBneg_20,
      gBneg_21,
      gBneg_22,
      gBneg_23,
      gBneg_24,
      gBneg_25,
      gBneg_26,
      gBneg_27,
      gBneg_28,
      gBneg_29,
      gBneg_30,
      gBneg_31,
      gBneg_32,
      gBneg_33,
      gBneg_34,
      gBneg_35,
      gBneg_36,
      gBneg_37,
      gBneg_38,
      gBneg_39,
      gBneg_40,
      gBneg_41,
      gBneg_42,
      gBneg_43,
      gBneg_44,
      gBneg_45,
      gBneg_46,
      gBneg_47,
      gBneg_48,
      gBneg_49,
      gBneg_50,
      gBneg_51,
      gBneg_52,
      gBneg_53,
      gBneg_54,
      gBneg_55,
      gBneg_56,
      gBneg_57,
      gBneg_58,
      gBneg_59,
      gBneg_60,
      gBneg_61,
      gBneg_62,
      gBneg_63]
  rwa [show (-1 : ℚ) + (((63 : ℕ) : ℚ) + 1) * (1 / 32) = 1 by norm_num] at h

theorem goodA : GoodA 0 XA := by
  have h := GoodA_of_chunks (a := 0) (δ := 7 / 4) le_rfl (by norm_num) 15 (by norm_num [XA])
    fun i hi => by
      interval_cases i
      exacts [gA_00, gA_01, gA_02, gA_03, gA_04, gA_05, gA_06, gA_07, gA_08, gA_09, gA_10, gA_11, gA_12, gA_13, gA_14, gA_15]
  rwa [show (0 : ℚ) + (((15 : ℕ) : ℚ) + 1) * (7 / 4) = XA by norm_num [XA]] at h

theorem BB_eq : (BB : ℝ) = 31.521 := by simp only [BB]; norm_num

/-- **`‖eta2DD t‖ ≤ 31.521` for `2πt ≥ 28`.** -/
theorem norm_eta2DD_le_of_ge {t : ℝ} (ht : 28 ≤ 2 * π * t) : ‖eta2DD t‖ ≤ 31.521 := by
  have ht0 : 0 < t := pos_of_mul_pos_right (by linarith : (0 : ℝ) < 2 * π * t) (by positivity)
  set w : ℝ := 1 / (2 * π * t) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ ((1 / 28 : ℚ) : ℝ) := by
    rw [hw]; push_cast
    exact one_div_le_one_div_of_le (by norm_num) ht
  have hR := norm_eta2DD_sub_FK ht0 KB
  rw [← hw] at hR
  obtain ⟨s, hs, m, hm, hz⟩ := exists_zm (norm_e (-(1 / 4 * t)))
  have hF : ‖FK KB (e (-(1 / 4 * t))) w‖ + RK KB w ≤ BB := by
    rw [hz]
    rcases hs with rfl | rfl
    · have := goodB_pos m w (by push_cast; exact hm.1) (by push_cast; exact hm.2)
        (by push_cast; exact hw0) hw1
      simpa using this
    · have := goodB_neg m w (by push_cast; exact hm.1) (by push_cast; exact hm.2)
        (by push_cast; exact hw0) hw1
      simpa using this
  have := norm_sub_norm_le (eta2DD t) (FK KB (e (-(1 / 4 * t))) w)
  rw [BB_eq] at hF
  linarith

/-- **`‖eta2DD t‖ ≤ 31.521` for `0 ≤ 2πt ≤ 28`.** -/
theorem norm_eta2DD_le_of_le {t : ℝ} (ht0 : 0 ≤ t) (ht : 2 * π * t ≤ 28) :
    ‖eta2DD t‖ ≤ 31.521 := by
  have h := goodA (2 * π * t) (by push_cast; positivity) (by simp only [XA]; push_cast; exact ht)
  have hπ : (2 * π * t) / (2 * π) = t := by field_simp
  rw [hπ, BB_eq] at h
  exact h

/-- **[H, (B.6)]**: `‖eta2DD t‖ ≤ 31.521` for all `t ≥ 0`. -/
theorem norm_eta2DD_le_31521 {t : ℝ} (ht : 0 ≤ t) : ‖eta2DD t‖ ≤ 31.521 := by
  rcases le_total (2 * π * t) 28 with h | h
  · exact norm_eta2DD_le_of_le ht h
  · exact norm_eta2DD_le_of_ge h

/-- As `TernaryGoldbach.MinorArcs.norm_fourier_eta2_neg` (in `InnerSums.lean`, which we do not
import). -/
theorem norm_fourier_eta2_neg' (t : ℝ) :
    ‖𝓕 (fun u => (eta2 u : ℂ)) (-t)‖ = ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e]
  have : (fun v => e (-(v * -t)) * (eta2 v : ℂ)) =
      fun v => (starRingEnd ℂ) (e (-(v * t)) * (eta2 v : ℂ)) := by
    funext v; rw [map_mul, conj_e, Complex.conj_ofReal, mul_neg, neg_neg]
  rw [this, integral_conj, Complex.norm_conj]

/-- **[H, Lemma B.1.2, (B.6)]**: `|η̂₂''|_∞ ≤ 31.521`, written as `(2πt)² |η̂₂(t)| ≤ 31.521`
(`η̂''(t) = (2πit)² η̂(t)`); the statement of `TernaryGoldbach.MinorArcs.eta2_fourier_bound'`
with `31.521` in place of `c₀ = 32`. -/
theorem eta2_fourier_bound_31521 (t : ℝ) :
    (2 * π * t) ^ 2 * ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ ≤ 31.521 := by
  wlog ht : 0 ≤ t generalizing t
  · have h := this (-t) (by linarith)
    rwa [norm_fourier_eta2_neg', show (2 * π * -t) ^ 2 = (2 * π * t) ^ 2 by ring] at h
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0; norm_num
  have hn : (2 * π * t) ^ 2 * ‖𝓕 (fun u => (eta2 u : ℂ)) t‖ = ‖eta2DD t‖ := by
    rw [← eta2DD_eq hpos.ne', norm_mul]
    congr 1
    rw [show ((2 * π * t) ^ 2 : ℂ) = (((2 * π * t) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hn]
  exact norm_eta2DD_le_31521 ht

end RSBounds.HelfgottB6
