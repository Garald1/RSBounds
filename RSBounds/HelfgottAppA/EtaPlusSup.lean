import TernaryGoldbach.MajorArcs.HHFourier
import TernaryGoldbach.Helfgott.SupNorms

/-!
# [H] (14.3) and (14.24): the sup norms of `η₊`

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2. For
`η₊(t) = h_H(t) t e^{-t²/2}` with `H = 200` (`TernaryGoldbach.Helfgott.etaPlus`), [H, (14.3)] states
`|η₊|_∞ ≤ 1.079955` and [H, (14.24)] states `|η₊ · t|_∞ ≤ 1.19073`. This file proves both
(`abs_etaPlus_le_1079955`, `mul_abs_etaPlus_le_119073`).

[H] derives them in Appendix A.5 from (A.36), `|h_H(t) − h(t)|/t < |h'|_∞ (1 + (4/π) log H)/H`.
(A.36) does not hold for very small `t`: `h_H(t)` decays only like `1/|log t|` as `t → 0⁺`, while
`h(t) ≍ t²`, and the proof of (A.36) bounds `e^{-w/H}` by `e^{-|w|/H}` also for `w < 0`. The two
sup norms are true all the same, with room to spare, by a different argument:

With `g(u) = h(eᵘ)`, `h_H(eᵘ)` is `g` with its Fourier transform cut off at `|ξ| ≤ H/2π`
(`TernaryGoldbach.MajorArcs.hH_eq_fourier`). By Fourier inversion,
`|h(t) − h_H(t)| ≤ ∫_{|ξ| > H/2π} |ĝ(ξ)| dξ`, and two integrations by parts give
`|ĝ(ξ)| ≤ ‖g''‖₁/(2πξ)²`, so `|h(t) − h_H(t)| ≤ ‖g''‖₁/(πH)`. Here
`g''(u) = eᵘ (t h'(t))'|_{t = eᵘ}` and `(t h'(t))' = e^{t−1/2} V(t)` with `|V| ≤ 13` on `[0, 2]`,
so `‖g''‖₁ ≤ 13 (e^{3/2} − e^{−1/2}) ≤ 50.4` and `|h − h_H| ≤ 0.0803` everywhere
(`abs_hBase_sub_hH200_le`). Then `|η₊(t)| ≤ (h(t) + 0.0803) t e^{-t²/2} ≤ 1 + 0.0803 · 0.616` and
`t |η₊(t)| ≤ (h(t) + 0.0803) t² e^{-t²/2} ≤ 1.106 + 0.0803 · 0.7358`.
-/

open Real MeasureTheory FourierTransform Set
open Complex (I)

namespace RSBounds.HelfgottAppA

open TernaryGoldbach.Helfgott (hBase hH etaPlus hP hP' hBase_eq_hP)
open TernaryGoldbach.MajorArcs (hBd gL gL' gC hasDerivAt_gL integrable_gL integrable_gL'
  integrable_gC differentiable_gC deriv_gC hBase_of_two_le)

/-! ## `g''` -/

/-- `Q(t) = t²(2 − t)²(1 − t)(4 + t)`, so that `t h'(t) = e^{t − 1/2} Q(t)`. -/
def Qp (t : ℝ) : ℝ := t ^ 2 * (2 - t) ^ 2 * (1 - t) * (4 + t)

/-- `Q'(t)`. -/
def Qp' (t : ℝ) : ℝ := 4 * t * (2 - t) * (1 - t) ^ 2 * (4 + t) - t ^ 2 * (2 - t) ^ 2 * (3 + 2 * t)

theorem hasDerivAt_Qp (t : ℝ) : HasDerivAt Qp (Qp' t) t := by
  have h := (((((hasDerivAt_pow 6 t).neg.add (hasDerivAt_pow 5 t)).add
    ((hasDerivAt_pow 4 t).const_mul 12)).sub ((hasDerivAt_pow 3 t).const_mul 28)).add
    ((hasDerivAt_pow 2 t).const_mul 16))
  convert h using 1
  · funext s; unfold Qp; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring
  · unfold Qp'; norm_num; ring

/-- `K(t) = t h'(t)` for `t ≤ 2`, and `0` beyond: `g'(u) = K(eᵘ)`. -/
noncomputable def Kf (t : ℝ) : ℝ := if t ≤ 2 then Real.exp (t - 1 / 2) * Qp t else 0

/-- `K'(t)`. -/
noncomputable def Kf' (t : ℝ) : ℝ := if t ≤ 2 then Real.exp (t - 1 / 2) * (Qp t + Qp' t) else 0

/-- `g''(u) = K'(eᵘ) eᵘ`. -/
noncomputable def gL'' (u : ℝ) : ℝ := Kf' (Real.exp u) * Real.exp u

theorem gL'_eq (u : ℝ) : gL' u = Kf (Real.exp u) := by
  unfold gL' hBd Kf
  split_ifs
  · unfold hP' Qp; ring
  · simp

theorem hasDerivAt_expQ (t : ℝ) :
    HasDerivAt (fun t => Real.exp (t - 1 / 2) * Qp t) (Real.exp (t - 1 / 2) * (Qp t + Qp' t)) t := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (t - 1 / 2)) (Real.exp (t - 1 / 2)) t := by
    have := (Real.hasDerivAt_exp (t - 1 / 2)).comp t ((hasDerivAt_id t).sub_const (1 / 2))
    convert this using 1
    · rfl
    · rw [mul_one]
  convert he.mul (hasDerivAt_Qp t) using 1
  ring

theorem Qp_two : Qp 2 = 0 := by unfold Qp; norm_num

theorem Qp'_two : Qp' 2 = 0 := by unfold Qp'; norm_num

theorem hasDerivAt_Kf (t : ℝ) : HasDerivAt Kf (Kf' t) t := by
  rcases lt_trichotomy t 2 with h | h | h
  · have : Kf =ᶠ[nhds t] fun t => Real.exp (t - 1 / 2) * Qp t := by
      filter_upwards [Iio_mem_nhds h] with s hs
      unfold Kf; rw [ite_eq_left hs.le]
    rw [Kf', ite_eq_left h.le]
    exact (hasDerivAt_expQ t).congr_of_eventuallyEq this
  · subst h
    have h0 : Kf' 2 = 0 := by unfold Kf'; rw [ite_eq_left le_rfl, Qp_two, Qp'_two]; simp
    rw [h0]
    have hl : HasDerivWithinAt Kf 0 (Iic 2) 2 := by
      have := (hasDerivAt_expQ 2).hasDerivWithinAt (s := Iic 2)
      rw [Qp_two, Qp'_two, add_zero, mul_zero] at this
      refine this.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s hs
        unfold Kf; rw [ite_eq_left (show s ≤ 2 from hs)]
      · unfold Kf; rw [ite_eq_left le_rfl]
    have hr : HasDerivWithinAt Kf 0 (Ici 2) 2 := by
      refine (hasDerivWithinAt_const (2:ℝ) (Ici 2) (0:ℝ)).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s hs
        unfold Kf
        rcases (show (2:ℝ) ≤ s from hs).eq_or_lt with e | e
        · subst e; rw [ite_eq_left le_rfl, Qp_two, mul_zero]
        · rw [ite_eq_right (not_le.2 e)]
      · unfold Kf; rw [ite_eq_left le_rfl, Qp_two, mul_zero]
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have : Kf =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      unfold Kf; rw [ite_eq_right (not_le.2 hs)]
    rw [Kf', ite_eq_right (not_le.2 h)]
    exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq this

theorem hasDerivAt_gL' (u : ℝ) : HasDerivAt gL' (gL'' u) u := by
  have hfun : gL' = fun u => Kf (Real.exp u) := funext gL'_eq
  rw [hfun]
  exact (hasDerivAt_Kf (Real.exp u)).comp u (Real.hasDerivAt_exp u)

/-- `|Q + Q'| ≤ 13` on `[0, 2]`: with `p = t(2 − t) ∈ [0, 1]` and `(1 − t)² = 1 − p`,
`|Q| ≤ 6p²` and `|Q'| ≤ 24p(1 − p) + 7p²`. -/
theorem abs_V_le {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) : |Qp t + Qp' t| ≤ 13 := by
  set p := t * (2 - t) with hp
  have hp0 : 0 ≤ p := by rw [hp]; nlinarith
  have hp1 : p ≤ 1 := by rw [hp]; nlinarith [sq_nonneg (t - 1)]
  have hu : (1 - t) ^ 2 = 1 - p := by rw [hp]; ring
  have h1t : |1 - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have eQ : Qp t = p ^ 2 * ((1 - t) * (4 + t)) := by unfold Qp; rw [hp]; ring
  have eQ' : Qp' t = 4 * p * (1 - p) * (4 + t) - p ^ 2 * (3 + 2 * t) := by
    unfold Qp'; rw [← hu, hp]; ring
  have hQ : |Qp t| ≤ 6 * p ^ 2 := by
    rw [eQ, abs_mul, abs_of_nonneg (sq_nonneg p), abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 4 + t)]
    have : |1 - t| * (4 + t) ≤ 6 := by nlinarith [abs_nonneg (1 - t)]
    nlinarith [sq_nonneg p]
  have hQ' : |Qp' t| ≤ 24 * p * (1 - p) + 7 * p ^ 2 := by
    rw [eQ']
    have a : 0 ≤ 4 * p * (1 - p) * (4 + t) := by
      have : 0 ≤ 1 - p := by linarith
      positivity
    have a' : 4 * p * (1 - p) * (4 + t) ≤ 24 * p * (1 - p) := by
      have : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
      nlinarith
    have b : 0 ≤ p ^ 2 * (3 + 2 * t) := by positivity
    have b' : p ^ 2 * (3 + 2 * t) ≤ 7 * p ^ 2 := by nlinarith [sq_nonneg p]
    rw [abs_le]; constructor <;> nlinarith
  calc |Qp t + Qp' t| ≤ |Qp t| + |Qp' t| := abs_add_le _ _
    _ ≤ 6 * p ^ 2 + (24 * p * (1 - p) + 7 * p ^ 2) := add_le_add hQ hQ'
    _ ≤ 13 := by nlinarith

/-- `|g''(u)| ≤ 13 e^{eᵘ − 1/2} eᵘ` where `eᵘ ≤ 2`, and `g''(u) = 0` beyond. -/
theorem abs_gL''_le (u : ℝ) :
    |gL'' u| ≤ (Iic (Real.log 2)).indicator (fun u => 13 * (Real.exp (Real.exp u - 1 / 2) * Real.exp u)) u := by
  unfold gL'' Kf'
  by_cases hu : Real.exp u ≤ 2
  · have hu' : u ∈ Iic (Real.log 2) := by
      rw [mem_Iic, ← Real.exp_le_exp, Real.exp_log (by norm_num)]; exact hu
    rw [ite_eq_left hu, indicator_of_mem hu']
    have hV := abs_V_le (Real.exp_pos u).le hu
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos u)]
    have h1 := Real.exp_pos (Real.exp u - 1 / 2)
    have h2 := Real.exp_pos u
    calc Real.exp (Real.exp u - 1 / 2) * |Qp (Real.exp u) + Qp' (Real.exp u)| * Real.exp u
        ≤ Real.exp (Real.exp u - 1 / 2) * 13 * Real.exp u := by gcongr
      _ = 13 * (Real.exp (Real.exp u - 1 / 2) * Real.exp u) := by ring
  · rw [ite_eq_right hu, zero_mul, abs_zero]
    exact indicator_nonneg (fun _ _ => by positivity) u

/-! ## `‖g''‖₁ ≤ 13 (e^{3/2} − e^{−1/2})` -/

/-- The majorant of `|g''|`. -/
noncomputable def Dg (u : ℝ) : ℝ :=
  (Iic (Real.log 2)).indicator (fun u => 13 * (Real.exp (Real.exp u - 1 / 2) * Real.exp u)) u

theorem integrableOn_Dg_core :
    IntegrableOn (fun u => 13 * (Real.exp (Real.exp u - 1 / 2) * Real.exp u)) (Iic (Real.log 2)) := by
  have hexp : IntegrableOn (fun u => 13 * Real.exp (3 / 2) * Real.exp u) (Iic (Real.log 2)) :=
    (integrableOn_exp_Iic (Real.log 2)).const_mul _
  refine hexp.mono' (by fun_prop : Continuous fun u => 13 * (Real.exp (Real.exp u - 1 / 2) *
    Real.exp u)).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun u hu => ?_)
  have hu' : Real.exp u ≤ 2 := by
    have := Real.exp_le_exp.2 (show u ≤ Real.log 2 from hu)
    rwa [Real.exp_log (by norm_num)] at this
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : Real.exp (Real.exp u - 1 / 2) ≤ Real.exp (3 / 2) := Real.exp_le_exp.2 (by linarith)
  have h0 := Real.exp_pos u
  nlinarith

theorem integrable_Dg : Integrable Dg :=
  integrableOn_Dg_core.integrable_indicator measurableSet_Iic

theorem integral_Dg : ∫ u, Dg u = 13 * (Real.exp (3 / 2) - Real.exp (-1 / 2)) := by
  unfold Dg
  rw [integral_indicator measurableSet_Iic]
  have hderiv : ∀ x ∈ Iio (Real.log 2), HasDerivAt (fun u => 13 * Real.exp (Real.exp u - 1 / 2))
      (13 * (Real.exp (Real.exp x - 1 / 2) * Real.exp x)) x := by
    intro x _
    have := ((Real.hasDerivAt_exp (Real.exp x - 1 / 2)).comp x
      ((Real.hasDerivAt_exp x).sub_const (1 / 2))).const_mul 13
    simpa using this
  have hcont : ContinuousWithinAt (fun u => 13 * Real.exp (Real.exp u - 1 / 2)) (Iic (Real.log 2))
      (Real.log 2) := (by fun_prop : Continuous fun u => 13 * Real.exp (Real.exp u - 1 / 2)).continuousWithinAt
  have htend : Filter.Tendsto (fun u => 13 * Real.exp (Real.exp u - 1 / 2)) Filter.atBot
      (nhds (13 * Real.exp (-1 / 2))) := by
    have h1 : Filter.Tendsto (fun u => Real.exp u - 1 / 2) Filter.atBot (nhds (0 - 1 / 2)) :=
      Real.tendsto_exp_atBot.sub_const _
    rw [show (0:ℝ) - 1 / 2 = -1 / 2 by norm_num] at h1
    exact ((Real.continuous_exp.tendsto _).comp h1).const_mul 13
  rw [integral_Iic_of_hasDerivAt_of_tendsto hcont hderiv integrableOn_Dg_core htend,
    Real.exp_log (by norm_num)]
  norm_num
  ring

theorem measurable_Kf' : Measurable Kf' := by
  unfold Kf'
  exact Measurable.ite measurableSet_Iic
    (by unfold Qp Qp'; fun_prop : Continuous fun t => Real.exp (t - 1 / 2) * (Qp t + Qp' t)).measurable
    measurable_const

theorem integrable_gL'' : Integrable gL'' := by
  refine integrable_Dg.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact ((measurable_Kf'.comp Real.measurable_exp).mul Real.measurable_exp).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_gL''_le u

/-- `‖g''‖₁ ≤ 50.4`. -/
theorem integral_abs_gL''_le : ∫ u, |gL'' u| ≤ 50.4 := by
  have h1 : ∫ u, |gL'' u| ≤ ∫ u, Dg u :=
    integral_mono integrable_gL''.abs integrable_Dg fun u => abs_gL''_le u
  have he1 : Real.exp (3 / 2) < 4.4817 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
    have hh : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2), Real.exp_pos 1]
  have he2 : 0.6065 < Real.exp (-1 / 2) := by
    have h := Real.exp_one_lt_d9
    have hh : Real.exp (-1 / 2) ^ 2 * Real.exp 1 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1 / 2), Real.exp_pos 1]
  rw [integral_Dg] at h1
  linarith

/-! ## The Fourier transform of `g` -/

theorem hasDerivAt_g'C (u : ℝ) : HasDerivAt (fun u => (gL' u : ℂ)) (gL'' u : ℂ) u :=
  (hasDerivAt_gL' u).ofReal_comp

theorem differentiable_g'C : Differentiable ℝ fun u => (gL' u : ℂ) :=
  fun u => (hasDerivAt_g'C u).differentiableAt

theorem deriv_g'C : deriv (fun u => (gL' u : ℂ)) = fun u => (gL'' u : ℂ) := by
  ext u; exact (hasDerivAt_g'C u).deriv

/-- `(2π|ξ|)² ‖ĝ(ξ)‖ ≤ ‖g''‖₁`. -/
theorem sq_mul_norm_fourier_gC_le (ξ : ℝ) : (2 * π * |ξ|) ^ 2 * ‖𝓕 gC ξ‖ ≤ ∫ u, |gL'' u| := by
  have hf1 := Real.fourier_deriv integrable_gC differentiable_gC
    (by rw [deriv_gC]; exact integrable_gL'.ofReal)
  rw [deriv_gC] at hf1
  have hf2 := Real.fourier_deriv integrable_gL'.ofReal differentiable_g'C
    (by rw [deriv_g'C]; exact integrable_gL''.ofReal)
  rw [deriv_g'C] at hf2
  have e : 𝓕 (fun u => (gL'' u : ℂ)) ξ = (2 * π * I * ξ) • ((2 * π * I * ξ) • 𝓕 gC ξ) := by
    rw [congrFun hf2 ξ, congrFun hf1 ξ]
  have hb := Real.norm_fourier_le_integral_norm (fun u => (gL'' u : ℂ)) ξ
  have hn : ‖(2 * π * I * ξ : ℂ)‖ = 2 * π * |ξ| := by
    rw [show (2 * π * I * ξ : ℂ) = ((2 * π * ξ : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [e, norm_smul, norm_smul, hn] at hb
  simp only [Complex.norm_real, Real.norm_eq_abs] at hb
  calc (2 * π * |ξ|) ^ 2 * ‖𝓕 gC ξ‖ = 2 * π * |ξ| * (2 * π * |ξ| * ‖𝓕 gC ξ‖) := by ring
    _ ≤ ∫ u, |gL'' u| := hb

theorem integrable_fourier_gC : Integrable (𝓕 gC) := by
  set C := ∫ u, ‖gC u‖
  set L := ∫ u, |gL'' u|
  have hL0 : 0 ≤ L := integral_nonneg fun u => abs_nonneg _
  have hC0 : 0 ≤ C := integral_nonneg fun u => norm_nonneg _
  have hπ := Real.pi_pos
  refine (integrable_inv_one_add_sq.const_mul (2 * (C + L / (4 * π ^ 2)))).mono'
    TernaryGoldbach.MajorArcs.continuous_fourier_gC.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  have h1 : ‖𝓕 gC ξ‖ ≤ C := Real.norm_fourier_le_integral_norm gC ξ
  have h2 := sq_mul_norm_fourier_gC_le ξ
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  rcases le_or_gt |ξ| 1 with hξ | hξ
  · have : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ξ]
    have hn := norm_nonneg (𝓕 gC ξ)
    have : 0 ≤ L / (4 * π ^ 2) := by positivity
    nlinarith
  · have hsq : 1 ≤ ξ ^ 2 := by rw [← sq_abs]; nlinarith
    have e : (2 * π * |ξ|) ^ 2 = 4 * π ^ 2 * ξ ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [e] at h2
    have h3 : ‖𝓕 gC ξ‖ * ξ ^ 2 ≤ L / (4 * π ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hn := norm_nonneg (𝓕 gC ξ)
    nlinarith

/-! ## `|h − h_H| ≤ ‖g''‖₁/(πH)` -/

/-- The integrand of a Fourier integral is integrable when the function is. -/
theorem integrable_exp_smul {f : ℝ → ℂ} (hf : Integrable f) (w : ℝ) :
    Integrable fun v => Complex.exp (↑(-2 * π * v * w) * I) • f v := by
  refine hf.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * I)).aestronglyMeasurable).smul
      hf.aestronglyMeasurable
  · rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The cut-off set `[−H/2π, H/2π]`. -/
def cutS (H : ℝ) : Set ℝ := Icc (-(H / (2 * π))) (H / (2 * π))

theorem norm_hBase_sub_hH_le {H t : ℝ} (hH0 : 0 < H) (ht : 0 < t) :
    |hBase t - hH H t| ≤ ∫ ξ in (cutS H)ᶜ, ‖𝓕 gC ξ‖ := by
  have hinv := (differentiable_gC.continuous).fourierInv_fourier_eq integrable_gC integrable_fourier_gC
  have e1 : (hBase t : ℂ) = 𝓕 (𝓕 gC) (-Real.log t) := by
    rw [← Real.fourierInv_eq_fourier_neg, hinv]
    simp only [gC, TernaryGoldbach.MajorArcs.gL, Real.exp_log ht]
  have e2 := TernaryGoldbach.MajorArcs.hH_eq_fourier_K hH0 ht
  have e3 : ((hBase t - hH H t : ℝ) : ℂ) = ∫ v, Complex.exp (↑(-2 * π * v * -Real.log t) * I) •
      (cutS H)ᶜ.indicator (𝓕 gC) v := by
    rw [Complex.ofReal_sub, e1, e2, Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul,
      ← integral_sub (integrable_exp_smul integrable_fourier_gC _)
        (integrable_exp_smul (TernaryGoldbach.MajorArcs.integrable_Kc H) _)]
    congr 1; ext v
    rw [← smul_sub, indicator_compl, Pi.sub_apply]
    rfl
  have hb : ‖((hBase t - hH H t : ℝ) : ℂ)‖ ≤ ∫ v, ‖(cutS H)ᶜ.indicator (𝓕 gC) v‖ := by
    rw [e3]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; ext v
    rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [Complex.norm_real, Real.norm_eq_abs] at hb
  refine hb.trans (le_of_eq ?_)
  simp_rw [norm_indicator_eq_indicator_norm]
  exact integral_indicator (measurableSet_Icc.compl)

/-- `∫_{|ξ| > H/2π} ‖ĝ‖ ≤ ‖g''‖₁/(πH)`. -/
theorem tail_le {H : ℝ} (hH0 : 0 < H) :
    ∫ ξ in (cutS H)ᶜ, ‖𝓕 gC ξ‖ ≤ (∫ u, |gL'' u|) / (π * H) := by
  set L := ∫ u, |gL'' u|
  set A := H / (2 * π)
  have hπ := Real.pi_pos
  have hA : 0 < A := by positivity
  set c := L / (4 * π ^ 2)
  have hL0 : 0 ≤ L := integral_nonneg fun u => abs_nonneg _
  -- the majorant `c ξ⁻² 1_{|ξ| > A}`
  set G : ℝ → ℝ := fun ξ => (Ioi A).indicator (fun x => c * x ^ (-2 : ℝ)) ξ +
    (Ioi A).indicator (fun x => c * x ^ (-2 : ℝ)) (-ξ)
  have hIoi : IntegrableOn (fun x : ℝ => c * x ^ (-2 : ℝ)) (Ioi A) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hA).const_mul c
  have hG1 : Integrable fun ξ => (Ioi A).indicator (fun x => c * x ^ (-2 : ℝ)) ξ :=
    hIoi.integrable_indicator measurableSet_Ioi
  have hG : Integrable G := hG1.add hG1.comp_neg
  have hval : ∫ ξ, G ξ = 2 * (c * A⁻¹) := by
    have h1 : ∫ ξ, (Ioi A).indicator (fun x => c * x ^ (-2 : ℝ)) ξ = c * A⁻¹ := by
      rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_Ioi_rpow_of_lt
        (by norm_num) hA]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring
    rw [integral_add hG1 hG1.comp_neg, integral_neg_eq_self
      (fun ξ => (Ioi A).indicator (fun x => c * x ^ (-2 : ℝ)) ξ) volume, h1]
    ring
  have hle : ∀ ξ, (cutS H)ᶜ.indicator (fun ξ => ‖𝓕 gC ξ‖) ξ ≤ G ξ := by
    intro ξ
    by_cases hξ : ξ ∈ (cutS H)ᶜ
    · rw [indicator_of_mem hξ]
      simp only [cutS, mem_compl_iff, mem_Icc, not_and_or, not_le] at hξ
      have habs : A < |ξ| := by
        rcases hξ with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · exact h.trans_le (le_abs_self ξ)
      have hξ0 : 0 < |ξ| := hA.trans habs
      have h2 := sq_mul_norm_fourier_gC_le ξ
      have hbound : ‖𝓕 gC ξ‖ ≤ c * |ξ| ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hξ0.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        have e : (2 * π * |ξ|) ^ 2 = 4 * π ^ 2 * |ξ| ^ 2 := by ring
        rw [e] at h2
        simp only [c]
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have hG0 : ∀ y, 0 ≤ (Ioi A).indicator (fun x => c * x ^ (-2 : ℝ)) y :=
        fun y => indicator_nonneg (fun x hx => mul_nonneg (by positivity)
          (Real.rpow_nonneg (hA.le.trans (le_of_lt hx)) _)) y
      rcases le_or_gt 0 ξ with hs | hs
      · have : ξ ∈ Ioi A := by rw [abs_of_nonneg hs] at habs; exact habs
        rw [abs_of_nonneg hs] at hbound
        simp only [G, indicator_of_mem this]
        linarith [hG0 (-ξ)]
      · have : -ξ ∈ Ioi A := by rw [abs_of_neg hs] at habs; exact habs
        rw [abs_of_neg hs] at hbound
        simp only [G, indicator_of_mem this]
        linarith [hG0 ξ]
    · rw [indicator_of_notMem hξ]
      exact add_nonneg (indicator_nonneg (fun x hx => mul_nonneg (by positivity)
          (Real.rpow_nonneg (hA.le.trans (le_of_lt hx)) _)) _)
        (indicator_nonneg (fun x hx => mul_nonneg (by positivity)
          (Real.rpow_nonneg (hA.le.trans (le_of_lt hx)) _)) _)
  have hint : ∫ ξ in (cutS H)ᶜ, ‖𝓕 gC ξ‖ = ∫ ξ, (cutS H)ᶜ.indicator (fun ξ => ‖𝓕 gC ξ‖) ξ :=
    (integral_indicator measurableSet_Icc.compl).symm
  rw [hint]
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => indicator_nonneg
    (fun _ _ => norm_nonneg _) ξ) hG (Filter.Eventually.of_forall hle)).trans ?_
  rw [hval]
  simp only [c, A]
  field_simp
  ring_nf
  exact le_rfl

/-! ## The sup norms of `η₊` -/

/-- **`|h(t) − h₂₀₀(t)| ≤ 0.0803`** for `t > 0`. -/
theorem abs_hBase_sub_hH200_le {t : ℝ} (ht : 0 < t) : |hBase t - hH 200 t| ≤ 0.0803 := by
  have h1 := norm_hBase_sub_hH_le (H := 200) (by norm_num) ht
  have h2 := tail_le (H := 200) (by norm_num)
  have h3 := integral_abs_gL''_le
  have hπ := Real.pi_gt_d2
  have h4 : (∫ u, |gL'' u|) / (π * 200) ≤ 50.4 / (3.14 * 200) :=
    div_le_div₀ (by norm_num) h3 (by norm_num) (by linarith)
  have h5 : (50.4 : ℝ) / (3.14 * 200) ≤ 0.0803 := by norm_num
  linarith

theorem hBase_nonneg (t : ℝ) : 0 ≤ hBase t := by
  unfold TernaryGoldbach.Helfgott.hBase
  split_ifs with h
  · have : 0 ≤ 2 - t := by linarith [h.2]
    positivity
  · exact le_rfl

/-- `h(t) t e^{-t²/2} ≤ 1`: it is `(t(2 − t))³ e^{-(t−1)²/2}` on `[0, 2]`. -/
theorem hBase_mul_le_one {t : ℝ} (ht : 0 ≤ t) : hBase t * (t * Real.exp (-t ^ 2 / 2)) ≤ 1 := by
  unfold TernaryGoldbach.Helfgott.hBase
  split_ifs with h
  · have hp0 : 0 ≤ t * (2 - t) := mul_nonneg ht (by linarith [h.2])
    have hp1 : t * (2 - t) ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
    have e : t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) * (t * Real.exp (-t ^ 2 / 2)) =
        (t * (2 - t)) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) := by
      rw [show (t * (2 - t)) ^ 3 = t ^ 2 * (2 - t) ^ 3 * t by ring, mul_assoc, mul_assoc,
        ← mul_assoc (Real.exp (t - 1 / 2)) t, mul_comm (Real.exp (t - 1 / 2)) t, mul_assoc t,
        ← Real.exp_add]
      ring_nf
    rw [e]
    have h1 : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (t - 1)])
    have h2 : (t * (2 - t)) ^ 3 ≤ 1 := pow_le_one₀ hp0 hp1
    have h3 : 0 ≤ Real.exp (-(t - 1) ^ 2 / 2) := (Real.exp_pos _).le
    nlinarith [pow_nonneg hp0 3]
  · simp

/-- `(1 + s)³ (1 − s)² ≤ 1.106` for `|s| ≤ 1` (the maximum is `3456/3125` at `s = 1/5`). -/
theorem cube_sq_le {s : ℝ} (h1 : -1 ≤ s) (h2 : s ≤ 1) : (1 + s) ^ 3 * (1 - s) ^ 2 ≤ 1.106 := by
  have hq : 0 ≤ -125 * s ^ 3 - 175 * s ^ 2 + 185 * s + 331 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + s) (by linarith : (0:ℝ) ≤ 1 - s),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + s) (by linarith : (0:ℝ) ≤ 1 - s))
        (by linarith : (0:ℝ) ≤ 1 + s), sq_nonneg s]
  have e : (3456 : ℝ) / 3125 - (1 + s) ^ 3 * (1 - s) ^ 2 =
      (s - 1 / 5) ^ 2 * ((-125 * s ^ 3 - 175 * s ^ 2 + 185 * s + 331) / 125) := by ring
  have : 0 ≤ (s - 1 / 5) ^ 2 * ((-125 * s ^ 3 - 175 * s ^ 2 + 185 * s + 331) / 125) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- `h(t) t² e^{-t²/2} ≤ 1.106`: it is at most `t (t(2 − t))² = (1 + s)³(1 − s)²`, `s = t − 1`. -/
theorem hBase_mul_sq_le {t : ℝ} (ht : 0 ≤ t) : hBase t * (t ^ 2 * Real.exp (-t ^ 2 / 2)) ≤ 1.106 := by
  unfold TernaryGoldbach.Helfgott.hBase
  split_ifs with h
  · have hp0 : 0 ≤ t * (2 - t) := mul_nonneg ht (by linarith [h.2])
    have hp1 : t * (2 - t) ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
    have e : t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) =
        t * (t * (2 - t)) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) := by
      have : Real.exp (t - 1 / 2) * Real.exp (-t ^ 2 / 2) = Real.exp (-(t - 1) ^ 2 / 2) := by
        rw [← Real.exp_add]; ring_nf
      calc t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) * (t ^ 2 * Real.exp (-t ^ 2 / 2))
          = t * (t * (2 - t)) ^ 3 * (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2 / 2)) := by ring
        _ = _ := by rw [this]
    rw [e]
    have h1 : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (t - 1)])
    have h3 : 0 ≤ Real.exp (-(t - 1) ^ 2 / 2) := (Real.exp_pos _).le
    have h4 : (t * (2 - t)) ^ 3 ≤ (t * (2 - t)) ^ 2 := by
      rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hp0 2) hp1
    have h5 : t * (t * (2 - t)) ^ 2 ≤ 1.106 := by
      have := cube_sq_le (s := t - 1) (by linarith) (by linarith [h.2])
      have e2 : (1 + (t - 1)) ^ 3 * (1 - (t - 1)) ^ 2 = t * (t * (2 - t)) ^ 2 := by ring
      linarith
    have h6 : 0 ≤ t * (t * (2 - t)) ^ 3 := mul_nonneg ht (pow_nonneg hp0 3)
    calc t * (t * (2 - t)) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) ≤ t * (t * (2 - t)) ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left h1 h6
      _ ≤ t * (t * (2 - t)) ^ 2 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h4 ht
      _ ≤ 1.106 := h5
  · norm_num

/-- `|h₂₀₀(t)| ≤ h(t) + 0.0803` for `t ≥ 0`. -/
theorem abs_hH200_le_hBase_add {t : ℝ} (ht : 0 ≤ t) : |hH 200 t| ≤ hBase t + 0.0803 := by
  rcases ht.eq_or_lt with h0 | ht
  · subst h0
    have : hH 200 0 = 0 := by unfold TernaryGoldbach.Helfgott.hH; simp [TernaryGoldbach.Helfgott.hBase]
    rw [this, abs_zero]; linarith [hBase_nonneg 0]
  · have h := abs_hBase_sub_hH200_le ht
    have h0 := hBase_nonneg t
    rw [abs_sub_comm] at h
    have := abs_sub_abs_le_abs_sub (hH 200 t) (hBase t)
    rw [abs_of_nonneg h0] at this
    linarith

/-- **[H, (14.3)]**: `|η₊(t)| ≤ 1.079955` for `t ≥ 0` (in fact `≤ 1.05`). -/
theorem abs_etaPlus_le_1079955 {t : ℝ} (ht : 0 ≤ t) : |etaPlus t| ≤ 1.079955 := by
  unfold TernaryGoldbach.Helfgott.etaPlus
  rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_hH200_le_hBase_add ht
  have h2 := hBase_mul_le_one ht
  have h3 := TernaryGoldbach.Helfgott.mul_exp_neg_sq_half_le t
  have e : -(1 / 2) * t ^ 2 = -t ^ 2 / 2 := by ring
  rw [e] at h3
  have h4 : 0 ≤ t * Real.exp (-t ^ 2 / 2) := by positivity
  calc |hH 200 t| * t * Real.exp (-t ^ 2 / 2) = |hH 200 t| * (t * Real.exp (-t ^ 2 / 2)) := by ring
    _ ≤ (hBase t + 0.0803) * (t * Real.exp (-t ^ 2 / 2)) := mul_le_mul_of_nonneg_right h1 h4
    _ = hBase t * (t * Real.exp (-t ^ 2 / 2)) + 0.0803 * (t * Real.exp (-t ^ 2 / 2)) := by ring
    _ ≤ 1 + 0.0803 * (1 / 1.625) := by gcongr
    _ ≤ 1.079955 := by norm_num

/-- **[H, (14.24)]**: `t |η₊(t)| ≤ 1.19073` for `t ≥ 0` (in fact `≤ 1.17`). -/
theorem mul_abs_etaPlus_le_119073 {t : ℝ} (ht : 0 ≤ t) : t * |etaPlus t| ≤ 1.19073 := by
  unfold TernaryGoldbach.Helfgott.etaPlus
  rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_hH200_le_hBase_add ht
  have h2 := hBase_mul_sq_le ht
  have h3 := TernaryGoldbach.Helfgott.phi_le_two_div_e t
  unfold TernaryGoldbach.Helfgott.phi at h3
  have h4 : 0 ≤ t ^ 2 * Real.exp (-t ^ 2 / 2) := by positivity
  calc t * (|hH 200 t| * t * Real.exp (-t ^ 2 / 2)) = |hH 200 t| * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
        ring
    _ ≤ (hBase t + 0.0803) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := mul_le_mul_of_nonneg_right h1 h4
    _ = hBase t * (t ^ 2 * Real.exp (-t ^ 2 / 2)) + 0.0803 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by ring
    _ ≤ 1.106 + 0.0803 * 0.7358 := by gcongr
    _ ≤ 1.19073 := by norm_num

end RSBounds.HelfgottAppA
