import RSBounds.HelfgottSmall.Assembly
import RSBounds.HelfgottSmall.AllChunks

/-!
# [H] (2.14) and (2.17) on the ranges below `2.5 · 10⁷`, unconditionally

Helfgott, *The ternary Goldbach problem* (arXiv:1501.05438v2), (2.14) and (2.17), on the finite
ranges that the walk covers. No hypothesis is needed: the walk is a finite computation.

* `psi_le_10004_small`: `ψ(y) ≤ 1.0004 y` for `2·10⁶ ≤ y ≤ 4·10⁶`;
* `sum_vonMangoldt_le_small`: the same with `∑_{1 ≤ n ≤ ⌊y⌋} Λ(n)`;
* `sum_vonMangoldt_mul_lt_small`: `∑_{1 ≤ n ≤ ⌊y⌋} Λ(n) n < 1.0008 y² / 2` for
  `1.6·10⁶ < y ≤ 2.5·10⁷`.
-/

namespace RSBounds.HelfgottSmall

open Real Finset ArithmeticFunction

theorem goodAt (m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ 25000000) : GoodAt m :=
  goodAt_all chunkGood_all m h1 h2

theorem psi_natCast (m : ℕ) : Chebyshev.psi m = psiS m := by
  rw [Chebyshev.psi, Nat.floor_natCast, psiS, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

theorem sum_vonMangoldt_le_small {y : ℝ} (h1 : 2000000 ≤ y) (h2 : y ≤ 4000000) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y := by
  have hy0 : 0 ≤ y := by linarith
  have hm1 : 2000000 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hm2 : ⌊y⌋₊ ≤ 4000000 := by
    have := Nat.floor_le_floor (R := ℝ) h2
    simpa using this
  have hmy : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have := (goodAt ⌊y⌋₊ (by omega) (by omega)).1 hm1 hm2
  unfold psiS at this
  linarith

theorem psi_le_10004_small {y : ℝ} (h1 : 2000000 ≤ y) (h2 : y ≤ 4000000) :
    Chebyshev.psi y ≤ 1.0004 * y := by
  have h := sum_vonMangoldt_le_small h1 h2
  rw [Chebyshev.psi_eq_psi_coe_floor, psi_natCast]
  exact h

theorem sum_vonMangoldt_mul_lt_small {y : ℝ} (h1 : 1600000 < y) (h2 : y ≤ 25000000) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hm1 : 1600000 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1.le)
  have hm2 : ⌊y⌋₊ ≤ 25000000 := by
    have := Nat.floor_le_floor (R := ℝ) h2
    simpa using this
  have hmy : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hm0 : (0 : ℝ) ≤ ⌊y⌋₊ := Nat.cast_nonneg _
  have := (goodAt ⌊y⌋₊ (by omega) (by omega)).2 hm1 hm2
  unfold sS at this
  have hsq : (⌊y⌋₊ : ℝ) ^ 2 ≤ y ^ 2 := by gcongr
  linarith

/-! ### Gluing to the ranges above, which need other inputs -/

/-- (2.14) from `2·10⁶`, given it from `4·10⁶`. -/
theorem psi_le_10004_of_ge (h4 : ∀ y : ℝ, 4000000 ≤ y → Chebyshev.psi y ≤ 1.0004 * y) {y : ℝ}
    (hy : 2000000 ≤ y) : Chebyshev.psi y ≤ 1.0004 * y := by
  rcases le_or_gt y 4000000 with h | h
  · exact psi_le_10004_small hy h
  · exact h4 y h.le

/-- (2.17) from `1.6·10⁶`, given it from `2.5·10⁷`. -/
theorem sum_vonMangoldt_mul_lt_of_ge
    (h25 : ∀ y : ℝ, 25000000 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2)
    {y : ℝ} (hy : 1600000 < y) : ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 := by
  rcases le_or_gt y 25000000 with h | h
  · exact sum_vonMangoldt_mul_lt_small hy h
  · exact h25 y h.le

end RSBounds.HelfgottSmall
