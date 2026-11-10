import Mathlib

/-! Elementary numerical inequalities for the deliberately conservative
large-x estimate with `log x >= 10^6`. -/

namespace TernaryGoldbach.RSBounds

theorem log_million_le_fourteen : Real.log (1e6 : ℝ) ≤ 14 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he : Real.exp 14 = Real.exp 1 ^ 14 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  calc (1e6 : ℝ) ≤ (2.7182818283 : ℝ) ^ 14 := by norm_num
    _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 14

theorem log_sq_million {L : ℝ} (hL : 1e6 ≤ L) :
    880 * (Real.log L) ^ 2 ≤ L := by
  have hL0 : 0 < L := by linarith
  set u := Real.log L - Real.log 1e6 with hu
  have hu0 : 0 ≤ u := sub_nonneg.2 (Real.log_le_log (by norm_num) hL)
  have hlog : Real.log L ≤ 14 + u := by
    dsimp [u]; linarith [log_million_le_fourteen]
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have he : L = 1e6 * Real.exp u := by
    rw [hu, Real.exp_sub, Real.exp_log hL0, Real.exp_log (by norm_num)]
    field_simp
  have ht := Real.quadratic_le_exp_of_nonneg hu0
  have hbound : 1e6 * (1 + u + u ^ 2 / 2) ≤ L := by
    rw [he]
    nlinarith
  have hs : (Real.log L) ^ 2 ≤ (14 + u) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  nlinarith [sq_nonneg u]

theorem middle_decay_million {L : ℝ} (hL : 1e6 ≤ L) :
    Real.exp (-(L / (20 * Real.log (L ^ 4 / 5)))) ≤ 1 / L ^ 11 := by
  have hL0 : 0 < L := by linarith
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hL4 : (1e24 : ℝ) ≤ L ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4
    norm_num at this ⊢
    exact this
  have hg0 : 0 < Real.log (L ^ 4 / 5) := Real.log_pos (by linarith)
  have hg : Real.log (L ^ 4 / 5) ≤ 4 * Real.log L := by
    rw [Real.log_div (pow_ne_zero _ hL0.ne') (by norm_num), Real.log_pow]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    norm_num
    linarith
  have hprod : (11 * Real.log L) * (20 * Real.log (L ^ 4 / 5)) ≤ L := by
    have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 220 * Real.log L by positivity)
    have hs := log_sq_million hL
    nlinarith
  have hquot : 11 * Real.log L ≤ L / (20 * Real.log (L ^ 4 / 5)) :=
    (le_div_iff₀ (by positivity)).2 hprod
  calc Real.exp (-(L / (20 * Real.log (L ^ 4 / 5))))
      ≤ Real.exp (-(11 * Real.log L)) := Real.exp_le_exp.2 (neg_le_neg hquot)
    _ = 1 / L ^ 11 := by
      rw [Real.exp_neg, show (11 : ℝ) * Real.log L = ((11 : ℕ) : ℝ) * Real.log L by norm_num,
        Real.exp_nat_mul, Real.exp_log hL0]
      simp only [one_div]

end TernaryGoldbach.RSBounds
