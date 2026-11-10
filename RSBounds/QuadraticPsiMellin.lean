/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import RSBounds.QuadraticPsi
import RSBounds.QuadraticMellin
import TernaryGoldbach.Explicit.ExplicitFormula

/-!
# The quadratic smoothed prime sum is the second primitive of psi

This is the arithmetic bridge between the canonical truncated-power sum
`QuadraticPsi.Psi2` and the Mellin-transform formulation. Compact support
makes the prime sum finite. No zero-location or analytic prime estimate is
assumed.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.QuadraticPsiMellin

open TernaryGoldbach.Explicit QuadraticPsi QuadraticMellin

/-- Compact support reduces the smoothed prime sum to its finite range. -/
theorem SsumG_quadratic_eq_finite {x : ℝ} (hx : 0 < x) :
    SsumG (1 : DirichletCharacter ℂ 1) weight x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (Λ n : ℂ) * weight (n / x) := by
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  unfold SsumG
  simp only [hchar, mul_one]
  apply tsum_eq_sum
  intro n hn
  have hnf : ⌊x⌋₊ < n := by
    simp only [mem_Icc, Nat.zero_le, true_and] at hn
    omega
  have hxn : x < n := (Nat.floor_lt hx.le).1 hnf
  have hratio : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).2 (by simpa using hxn.le)
  rw [weight_eq_zero_of_one_le hratio, mul_zero]

/-- Scaling the quadratic weight recovers the truncated-power primitive. -/
theorem scaled_weight_eq_quadraticPrimitive {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (x : ℂ) ^ 2 * weight (a / x) = (quadraticPrimitive (x - a) : ℂ) := by
  have hmax : x * max (1 - a / x) 0 = max (x - a) 0 := by
    rw [mul_max_of_nonneg _ _ hx.le, mul_zero]
    congr 1
    field_simp [hx.ne'] <;> ring
  have hre : x ^ 2 * ((max (1 - a / x) 0) ^ 2 / 2) =
      quadraticPrimitive (x - a) := by
    rw [quadraticPrimitive, ← hmax, mul_pow]
    ring
  unfold weight
  exact_mod_cast hre

/-- The exact conversion from the Mellin smoothed prime sum to `Psi2`. -/
theorem pow_two_mul_SsumG_quadratic_eq_Psi2 {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ 2 * SsumG (1 : DirichletCharacter ℂ 1) weight x =
      (Psi2 x : ℂ) := by
  rw [SsumG_quadratic_eq_finite hx, mul_sum]
  unfold Psi2 psi2Trunc
  push_cast
  apply sum_congr rfl
  intro n _
  calc
    (x : ℂ) ^ 2 * ((Λ n : ℂ) * weight (n / x)) =
        (Λ n : ℂ) * ((x : ℂ) ^ 2 * weight (n / x)) := by ring
    _ = (Λ n : ℂ) * (quadraticPrimitive (x - n) : ℂ) := by
      rw [scaled_weight_eq_quadraticPrimitive hx]

end TernaryGoldbach.RSBounds.QuadraticPsiMellin
