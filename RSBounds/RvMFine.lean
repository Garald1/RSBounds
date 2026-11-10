/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.BacklundLowScalarBase
import RSBounds.BacklundLowMainTerm

/-!
# Main-term certificates with `3.141592 < π < 3.141593`

`BacklundLowScalar.MainCert.Valid` encloses `t/(2π)` using `3.14 < π < 22/7`. Near `t = 5000`
that leaves `rosserF t` uncertain by about `5`, and near `t = 170` the bound `|N − F| < 1` has only
`0.002` to spare. `FineValid` is the same check with Mathlib's `Real.pi_gt_d6` and
`Real.pi_lt_d6`. The certificate type and the logarithm checker are unchanged.
-/

open Real

namespace TernaryGoldbach.RSBounds.RvMFine
open BacklundLowScalar

/-- `MainCert.Valid` with `2π` enclosed in `[6.283184, 6.283186]`. -/
def FineValid (c : MainCert) : Prop :=
  c.lower.Valid ∧ c.upper.Valid ∧
  1 < c.lower.ratio ∧ 0 ≤ c.upper.ratio ∧
  c.lower.ratio * (3141593 / 500000 : ℚ) ≤ c.t ∧
  c.t ≤ c.upper.ratio * (3141592 / 500000 : ℚ) ∧
  c.lo < c.lower.ratio * c.lower.lower - c.upper.ratio + 7 / 8 ∧
  c.upper.ratio * c.upper.upper - c.lower.ratio + 7 / 8 < c.hi

instance (c : MainCert) : Decidable (FineValid c) := by unfold FineValid; infer_instance

lemma fine_sound {c : MainCert} (hc : FineValid c) :
    (c.lo : ℝ) < rosserF (c.t : ℝ) ∧ rosserF (c.t : ℝ) < (c.hi : ℝ) := by
  rcases hc with ⟨hlv, huv, hl1, hu0, hlt, hut, hlow, hupp⟩
  have hl1' : (1 : ℝ) < (c.lower.ratio : ℝ) := by exact_mod_cast hl1
  have hu0' : (0 : ℝ) ≤ (c.upper.ratio : ℝ) := by exact_mod_cast hu0
  have hlt' : (c.lower.ratio : ℝ) * (3141593 / 500000) ≤ (c.t : ℝ) := by
    have hh : c.lower.ratio * 3141593 ≤ c.t * 500000 := by linarith
    have hh' : (c.lower.ratio : ℝ) * 3141593 ≤ (c.t : ℝ) * 500000 := by exact_mod_cast hh
    linarith
  have hut' : (c.t : ℝ) ≤ (c.upper.ratio : ℝ) * (3141592 / 500000) := by
    have hh : c.t * 500000 ≤ c.upper.ratio * 3141592 := by linarith
    have hh' : (c.t : ℝ) * 500000 ≤ (c.upper.ratio : ℝ) * 3141592 := by exact_mod_cast hh
    linarith
  have hl0 : (0 : ℝ) < (c.lower.ratio : ℝ) := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hql : (c.lower.ratio : ℝ) ≤ (c.t : ℝ) / (2 * Real.pi) := by
    rw [le_div_iff₀ hp]
    have hπ : 2 * Real.pi ≤ (3141593 / 500000 : ℝ) := by linarith [Real.pi_lt_d6]
    exact (mul_le_mul_of_nonneg_left hπ hl0.le).trans hlt'
  have hqu : (c.t : ℝ) / (2 * Real.pi) ≤ (c.upper.ratio : ℝ) := by
    rw [div_le_iff₀ hp]
    have hπ : (3141592 / 500000 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_d6]
    exact hut'.trans (mul_le_mul_of_nonneg_left hπ hu0')
  have hq0 : (0 : ℝ) < (c.t : ℝ) / (2 * Real.pi) := hl0.trans_le hql
  have hll := (LogCert.log_bounds hlv).1
  have hlu := (LogCert.log_bounds huv).2
  have hlogl : (c.lower.lower : ℝ) ≤ Real.log ((c.t : ℝ) / (2 * Real.pi)) :=
    hll.trans (Real.log_le_log hl0 hql)
  have hlogu : Real.log ((c.t : ℝ) / (2 * Real.pi)) ≤ (c.upper.upper : ℝ) :=
    (Real.log_le_log hq0 hqu).trans hlu
  have hpL := mul_le_mul hql hlogl c.lower.lower_nonneg hq0.le
  have hpU := mul_le_mul hqu hlogu (Real.log_nonneg (hl1'.le.trans hql)) hu0'
  have hlo' : (c.lo : ℝ) < (c.lower.ratio : ℝ) * (c.lower.lower : ℝ) -
      (c.upper.ratio : ℝ) + 7 / 8 := by
    have hh : 8 * c.lo < 8 * (c.lower.ratio * c.lower.lower - c.upper.ratio) + 7 := by linarith
    have hh' : (8 : ℝ) * (c.lo : ℝ) <
        8 * ((c.lower.ratio : ℝ) * (c.lower.lower : ℝ) - (c.upper.ratio : ℝ)) + 7 := by
      exact_mod_cast hh
    linarith
  have hup' : (c.upper.ratio : ℝ) * (c.upper.upper : ℝ) -
      (c.lower.ratio : ℝ) + 7 / 8 < (c.hi : ℝ) := by
    have hh : 8 * (c.upper.ratio * c.upper.upper - c.lower.ratio) + 7 < 8 * c.hi := by linarith
    have hh' : (8 : ℝ) * ((c.upper.ratio : ℝ) * (c.upper.upper : ℝ) -
        (c.lower.ratio : ℝ)) + 7 < 8 * (c.hi : ℝ) := by exact_mod_cast hh
    linarith
  unfold rosserF
  constructor <;> linarith

end TernaryGoldbach.RSBounds.RvMFine
