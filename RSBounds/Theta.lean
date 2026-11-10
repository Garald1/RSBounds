import TernaryGoldbach.Explicit.ZeroFreeRegion

/-!
# A zero-free region from height 1894438.5122

This adapts the pinned dependency's Stechkin argument, with sigma = 1 + .2/log t.
The result is unconditional and does not use finite RH.
-/
open Complex Set Metric Filter MeasureTheory
open scoped Real Interval Topology ComplexConjugate ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds
open TernaryGoldbach.Explicit

set_option maxHeartbeats 1000000 in
/-- **Zero-free region** (Stechkin-type, `R = 20`): every zero `ρ = β + iγ` of `ξ` with `γ ≥ 1894438.5122` has
`β ≤ 1 − 1/(20 log γ)`. -/
theorem zero_free_pos_rs_height {ρ : ℂ} (hρ : xiF ρ = 0) (ht : 1894438.5122 ≤ ρ.im) :
    ρ.re ≤ 1 - 1 / (20 * Real.log ρ.im) := by
  obtain ⟨t, htdef⟩ : ∃ t, t = ρ.im := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log t := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β, β = ρ.re := ⟨_, rfl⟩
  rw [← htdef] at ht ⊢
  rw [← hLdef, ← hβdef]
  have ht0 : 0 < t := by linarith
  have hlogA : 14 ≤ Real.log (1894438.5122 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have he : Real.exp 14 = Real.exp 1 ^ 14 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 14
      _ ≤ 1894438.5122 := by norm_num
  have hL : 14 ≤ L := hLdef ▸ hlogA.trans (Real.log_le_log (by norm_num) ht)
  have hL0 : 0 < L := by linarith
  by_contra hβ
  push Not at hβ
  have hz := xiF_zero_re hρ
  have hβ1 : β < 1 := hβdef ▸ hz.2
  have h11 : 1 / (20 * L) ≤ 0.05 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hβ95 : 0.95 ≤ β := by linarith
  have hβh : ρ.re ≠ 1 / 2 := by intro h; rw [← hβdef] at h; linarith
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = 1 + 0.2 / L := ⟨_, rfl⟩
  have hσL0 : 0 < 0.2 / L := by positivity
  have hσ1 : 1 < σ := by linarith
  have hσL : 0.2 / L ≤ 0.0155 := by rw [div_le_iff₀ hL0]; linarith
  have hσ2 : σ ≤ 1.0155 := by linarith
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = (σ - 1 / 2) / (1.6181 - 1 / 2) := ⟨_, rfl⟩
  have hκl : 0.4471 ≤ κ := by rw [hκ, le_div_iff₀ (by norm_num)]; norm_num; linarith
  have hκu : κ ≤ 0.46105 := by rw [hκ, div_le_iff₀ (by norm_num)]; norm_num; linarith
  -- numerical constants
  have lπ := log_pi_ge
  have lπu := log_pi_le
  have l2 := log2_le'
  have l2' := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have l3 := log3_le'
  have l3' := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  -- `log2508_le` became `log2585_le` (`log 2.5085 ≤ 0.9197`) upstream at `192ca57`
  have l2508 : Real.log 2.508 ≤ 0.9197 :=
    (Real.log_le_log (by norm_num) (by norm_num)).trans log2585_le
  -- tiny terms
  have tt : ∀ j : ℝ, 1 ≤ j → 2 / (j * t) ^ 2 + 1 / 2 * κ * (0.20604 + 11 / (j * t) ^ 2) ≤ 1 / 2 * κ * 0.20604 + 1e-11 := by
    intro j hj
    have hjt : 1 * 1894438.5122 ≤ j * t := mul_le_mul hj ht (by norm_num) (by linarith)
    have hsq : (1e6 : ℝ) ^ 2 ≤ (j * t) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hsq' : (1e12 : ℝ) ≤ (j * t) ^ 2 := by norm_num at hsq ⊢; linarith
    have a : 2 / (j * t) ^ 2 ≤ 2 / 1e12 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq'
    have b : 11 / (j * t) ^ 2 ≤ 11 / 1e12 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq'
    have c : κ * (11 / (j * t) ^ 2) ≤ 1 * (11 / 1e12) :=
      mul_le_mul (by linarith) b (by positivity) (by norm_num)
    have e : 2 / (j * t) ^ 2 + 1 / 2 * κ * (0.20604 + 11 / (j * t) ^ 2) =
        1 / 2 * κ * 0.20604 + (2 / (j * t) ^ 2 + 1 / 2 * (κ * (11 / (j * t) ^ 2))) := by ring
    rw [e]
    norm_num at a c ⊢
    linarith
  have t1 := tt 1 le_rfl
  have t2 := tt 2 (by norm_num)
  have t3 := tt 3 (by norm_num)
  have t4 := tt 4 (by norm_num)
  rw [one_mul] at t1
  -- the zero term
  have hsb : 0 < σ - β := by linarith
  have hsb' : σ - β ≤ 0.25 / L := by
    have h1 : σ - β < 0.2 / L + 1 / (20 * L) := by linarith only [hβ, hσ]
    have e : 0.2 / L + 1 / (20 * L) = (0.2 + 1 / 20) / L := by field_simp
    have e2 : (0.2 + 1 / 20) / L ≤ 0.25 / L := div_le_div_of_nonneg_right (by norm_num) hL0.le
    linarith
  have hZ1 : 4 * L ≤ 1 / (σ - β) := by
    rw [le_div_iff₀ hsb]; rw [le_div_iff₀ hL0] at hsb'; linarith only [hsb']
  have hZ2 : 1 / σ ≤ 1 / (σ + β - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hZ3 : 1 / (1.6181 - β) ≤ 1 / 0.6181 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hZ4 : 1 / (1.6181 + β - 1) ≤ 1 / 1.5681 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hσinv : 0.9847 ≤ 1 / σ := by rw [le_div_iff₀ (by linarith)]; linarith only [hσ2]
  have hσinv2 : 1.96947 ≤ 2 / σ := by rw [le_div_iff₀ (by linarith)]; linarith only [hσ2]
  have hσinv3 : 0.6632 ≤ 1 / (σ / 2 + 1) := by rw [le_div_iff₀ (by linarith)]; linarith only [hσ2]
  have hσ1L : 1 / (σ - 1) = 5 * L := by rw [hσ]; field_simp; ring
  have hlogσ : Real.log (σ / 2 + 2) ≤ 0.9197 := (Real.log_le_log (by linarith) (by linarith)).trans l2508
  have hσinv1 : 1 / σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  -- products with `κ`
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = 1 / 1.6181 + 1 / (1.6181 - 1) - 1 / 2 * Real.log π +
      1 / 2 * (Real.log (1.6181 / 2 + 2) - 2 / 1.6181 - 1 / (1.6181 / 2 + 1)) := ⟨_, rfl⟩
  have hE1u : E1 ≤ 1.2857 := by
    have := log280905_le
    rw [hE1, show (1.6181 : ℝ) / 2 + 2 = 2.80905 by norm_num]; norm_num; linarith
  have hE1l : 0 ≤ E1 := by
    rw [hE1, show (1.6181 : ℝ) / 2 + 2 = 2.80905 by norm_num]
    have : 0 ≤ Real.log 2.80905 := Real.log_nonneg (by norm_num)
    norm_num; linarith
  have pE : κ * E1 ≤ 0.5928 := by
    calc κ * E1 ≤ 0.46105 * E1 := mul_le_mul_of_nonneg_right hκu hE1l
      _ ≤ 0.46105 * 1.2857 := by gcongr
      _ ≤ 0.5928 := by norm_num
  have pW : ∀ X : ℝ, 0 ≤ X → (1 - κ) * X ≤ 0.5529 * X := fun X hX =>
    mul_le_mul_of_nonneg_right (by linarith) hX
  have pW1 := pW (1 / 2 * L + 0.36 - 1 / 2 * Real.log π) (by linarith)
  have pW2 := pW (1 / 2 * (Real.log 2 + L) + 0.36 - 1 / 2 * Real.log π) (by linarith)
  have pW3 := pW (1 / 2 * (Real.log 3 + L) + 0.36 - 1 / 2 * Real.log π) (by linarith)
  have pW4 := pW (1 / 2 * (2 * Real.log 2 + L) + 0.36 - 1 / 2 * Real.log π) (by linarith)
  have pZ : κ * (1 / (1.6181 - β) + 1 / (1.6181 + β - 1)) ≤ 1.04 := by
    have : 0 ≤ 1 / (1.6181 - β) + 1 / (1.6181 + β - 1) := by
      have : 0 < 1.6181 - β := by linarith
      have : 0 < 1.6181 + β - 1 := by linarith
      positivity
    calc κ * (1 / (1.6181 - β) + 1 / (1.6181 + β - 1)) ≤ 0.46105 * (1 / (1.6181 - β) + 1 / (1.6181 + β - 1)) :=
          mul_le_mul_of_nonneg_right hκu this
      _ ≤ 0.46105 * (1 / 0.6181 + 1 / 1.5681) := by gcongr
      _ ≤ 1.04 := by norm_num
  -- the positivity and the five terms
  have hP := vM_positivity hσ1 t
  rw [show (0:ℝ) * t = 0 by ring, show (1:ℝ) * t = t by ring] at hP
  have h0 := vM_real_le hσ1
  rw [hσ1L] at h0
  have Z1 := stech_wrap_rho hσ1 (by linarith) hρ hβh
  rw [← htdef, ← hβdef] at Z1
  have h1 := vM_term_le hσ1 (by linarith) (show (10:ℝ) ≤ t by linarith) Z1
  have h2 := vM_term_le (τ := 2 * t) hσ1 (by linarith) (by linarith) (stech_wrap (τ := 2 * t) hσ1 (by linarith))
  have h3 := vM_term_le (τ := 3 * t) hσ1 (by linarith) (by linarith) (stech_wrap (τ := 3 * t) hσ1 (by linarith))
  have h4 := vM_term_le (τ := 4 * t) hσ1 (by linarith) (by linarith) (stech_wrap (τ := 4 * t) hσ1 (by linarith))
  rw [← hκ, ← hE1] at h1 h2 h3 h4
  have lt2 : Real.log (2 * t) = Real.log 2 + L := by rw [Real.log_mul (by norm_num) ht0.ne', hLdef]
  have lt3 : Real.log (3 * t) = Real.log 3 + L := by rw [Real.log_mul (by norm_num) ht0.ne', hLdef]
  have lt4 : Real.log (4 * t) = 2 * Real.log 2 + L := by
    rw [Real.log_mul (by norm_num) ht0.ne', show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow, hLdef]; push_cast; ring
  rw [← hLdef] at h1
  rw [lt2] at h2
  rw [lt3] at h3
  rw [lt4] at h4
  linarith only [hP, h0, h1, h2, h3, h4, t1, t2, t3, t4, hZ1, hZ2, hσinv, hσinv1, hσinv2, hσinv3, hlogσ,
    lπ, l2, l3, pE, pW1, pW2, pW3, pW4, pZ, hκu, hκl, hL]

/-- **Zero-free region**: every zero `ρ = β + iγ` of `ξ` (equivalently a nontrivial zero of `ζ`) with
`|γ| ≥ 1894438.5122` has `β ≤ 1 − 1/(20 log|γ|)`. -/
theorem zero_free_rs_height {ρ : ℂ} (hρ : xiF ρ = 0) (ht : 1894438.5122 ≤ |ρ.im|) :
    ρ.re ≤ 1 - 1 / (20 * Real.log |ρ.im|) := by
  rcases le_or_gt 0 ρ.im with h | h
  · rw [abs_of_nonneg h] at ht ⊢; exact zero_free_pos_rs_height hρ ht
  · have hc : xiF (conj ρ) = 0 := by rw [xiF_conj, hρ, map_zero]
    have := zero_free_pos_rs_height hc (by simpa [abs_of_neg h] using ht)
    simpa [abs_of_neg h] using this


/-- Standard-zeta formulation of the same unconditional zero-free region. -/
theorem riemannZeta_zero_free_rs_height {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hρ : riemannZeta ρ = 0) (ht : 1894438.5122 ≤ |ρ.im|) :
    ρ.re ≤ 1 - 1 / (20 * Real.log |ρ.im|) :=
  zero_free_rs_height ((xiF_eq_zero_iff h0 h1).2 hρ) ht

end TernaryGoldbach.RSBounds
