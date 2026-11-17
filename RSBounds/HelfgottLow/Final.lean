import RSBounds.HelfgottLow.Assembly
import RSBounds.HelfgottLow.AllChunks

/-!
# [H] (2.16), (2.18) and (2.19) on their book ranges

Helfgott, *The ternary Goldbach problem* (arXiv:1501.05438v2), §2.3:

* (2.16) `∑_{n ≤ y} Λ(n) n < 1.03884 y² / 2` for `y > 663`;
* (2.18) `∑_{n ≤ y} Λ(n) / √n < 2 · 1.0004 √y` for `y ≥ 1`;
* (2.19) `∑_{y/2 < p ≤ y} (log p)² ≤ y log y / 2` for `y ≥ 117`.

The walk gives each of them unconditionally up to `2·10⁶` (`…_small`). Above that:

* (2.16) follows from (2.17) for `y > 1.6·10⁶`, since `1.0008 < 1.03884`
  (`sum_vonMangoldt_mul_lt_a16_of`);
* (2.18) follows from (2.14) for `y ≥ 2·10⁶` by summation by parts, starting from the walk's
  closing bound on `∑_{n ≤ 2·10⁶} Λ(n) (1/√n - 1/√(2·10⁶))` (`sum_vonMangoldt_div_sqrt_lt_of`);
* (2.19) for `y ≥ 2·10⁶` is an input (`sum_log_sq_primes_le_of`); it is stated as in
  `TernaryGoldbach.Prelim.sum_log_sq_primes_le`.

The glue lemmas take the large-`y` statements as hypotheses, in the forms that
`HelfgottPsiBoundsBook` proves (2.14) and (2.17).
-/

namespace RSBounds.HelfgottLow

open Real Finset ArithmeticFunction
open RSBounds.HelfgottSmall (SC SC_pos psiS sS psiS_succ)

theorem goodAt (m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ 2000000) : GoodAt m :=
  goodAt_all chunkGood_all m h1 h2

theorem bS_N0 : bS 2000000 < 1.0004 * √(2000000 : ℝ) := by
  have := bS_final chunkGood_all
  simpa [N0] using this

/-! ### (2.16) -/

/-- **[H, (2.16)]** for `663 < y ≤ 1.6·10⁶`, unconditionally. -/
theorem sum_vonMangoldt_mul_lt_a16_small {y : ℝ} (h1 : 663 < y) (h2 : y ≤ 1600000) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.03884 * y ^ 2 / 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hm1 : 663 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1.le)
  have hm2 : ⌊y⌋₊ ≤ 1600000 := by
    have := Nat.floor_le_floor (R := ℝ) h2
    simpa using this
  have hmy : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hm0 : (0 : ℝ) ≤ ⌊y⌋₊ := Nat.cast_nonneg _
  have := (goodAt ⌊y⌋₊ (by omega) (by omega)).1 hm1 hm2
  unfold sS at this
  have hsq : (⌊y⌋₊ : ℝ) ^ 2 ≤ y ^ 2 := by gcongr
  linarith

/-- **[H, (2.16)]** for `y > 663`, given (2.17) for `y > 1.6·10⁶`. -/
theorem sum_vonMangoldt_mul_lt_a16_of
    (h17 : ∀ y : ℝ, 1.6e6 < y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2)
    {y : ℝ} (hy : 663 < y) : ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.03884 * y ^ 2 / 2 := by
  rcases le_or_gt y 1600000 with h | h
  · exact sum_vonMangoldt_mul_lt_a16_small hy h
  · have := h17 y (by norm_num; linarith)
    have : 0 ≤ y ^ 2 := sq_nonneg y
    linarith

/-! ### (2.18) -/

theorem tS_one : tS 1 = 0 := by simp [tS]

/-- **[H, (2.18)]** for `1 ≤ y < 2·10⁶ + 1`, unconditionally. -/
theorem sum_vonMangoldt_div_sqrt_lt_small {y : ℝ} (h1 : 1 ≤ y) (h2 : y < 2000001) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / √(n : ℝ) < 2 * 1.0004 * √y := by
  have hy0 : 0 ≤ y := by linarith
  have hm1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hm2 : ⌊y⌋₊ ≤ 2000000 := by
    have := Nat.floor_lt hy0 |>.mpr (show y < ((2000001 : ℕ) : ℝ) by exact_mod_cast h2)
    omega
  have hmy : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hsy : √(⌊y⌋₊ : ℝ) ≤ √y := Real.sqrt_le_sqrt hmy
  have hy1 : 0 < √y := Real.sqrt_pos.mpr (by linarith)
  change tS ⌊y⌋₊ < _
  rcases Nat.lt_or_ge ⌊y⌋₊ 2 with h | h
  · have : ⌊y⌋₊ = 1 := by omega
    rw [this, tS_one]
    positivity
  · have := (goodAt ⌊y⌋₊ h hm2).2.1
    linarith

theorem bS_eq (N : ℕ) : bS N = tS N - RHO0 / SC * psiS N := by
  unfold bS tS psiS
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem psiS_nonneg (N : ℕ) : 0 ≤ psiS N := by
  unfold psiS
  exact Finset.sum_nonneg fun m _ => by exact_mod_cast vonMangoldt_nonneg

/-- `N (1/√N - 1/√(N+1)) ≤ √(N+1) - √N`. -/
theorem mul_inv_sqrt_sub_le (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * (1 / √(N : ℝ) - 1 / √((N + 1 : ℕ) : ℝ)) ≤ √((N + 1 : ℕ) : ℝ) - √(N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set u := √(N : ℝ) with hu
  set v := √((N + 1 : ℕ) : ℝ) with hv
  have hu0 : 0 < u := Real.sqrt_pos.mpr hN'
  have hv0 : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hu2 : u ^ 2 = N := Real.sq_sqrt hN'.le
  have hv2 : v ^ 2 = N + 1 := by rw [hv, Real.sq_sqrt (by positivity)]; push_cast; ring
  rw [← hu2]
  have e : u ^ 2 * (1 / u - 1 / v) = u - u ^ 2 / v := by field_simp
  rw [e]
  have : 2 * u - v ≤ u ^ 2 / v := by
    rw [le_div_iff₀ hv0]
    nlinarith [sq_nonneg (u - v)]
  linarith

/-- The summation by parts above `2·10⁶`: (2.18) at integers `N ≥ 2·10⁶`, given
`ψ(N) ≤ 1.0004 N` there. -/
theorem tS_lt_of_psi (h14 : ∀ N : ℕ, 2000000 ≤ N → psiS N ≤ 1.0004 * N) {N : ℕ}
    (hN : 2000000 ≤ N) : tS N < 2.0008 * √(N : ℝ) := by
  let G : ℕ → ℝ := fun M => tS M - psiS M / √(M : ℝ)
  have hG0 : G 2000000 ≤ bS 2000000 := by
    have hρ := rho_le (n := 2000000) (by norm_num) (by norm_num [N0])
    have hp := psiS_nonneg 2000000
    show tS 2000000 - psiS 2000000 / √((2000000 : ℕ) : ℝ) ≤ bS 2000000
    rw [bS_eq]
    have : RHO0 / SC * psiS 2000000 ≤ psiS 2000000 / √((2000000 : ℕ) : ℝ) := by
      rw [div_eq_mul_one_div (psiS 2000000), mul_comm (psiS 2000000)]
      exact mul_le_mul_of_nonneg_right hρ hp
    linarith
  have hstep : ∀ M : ℕ, 2000000 ≤ M → G (M + 1) ≤ G M + 1.0004 * (√((M + 1 : ℕ) : ℝ) - √(M : ℝ)) := by
    intro M hM
    have hM0 : 0 < M := by omega
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
    have hpsi := h14 M hM
    have hp0 := psiS_nonneg M
    have hfac : 0 ≤ 1 / √(M : ℝ) - 1 / √((M + 1 : ℕ) : ℝ) := by
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hM')
      exact Real.sqrt_le_sqrt (by push_cast; linarith)
    have key := mul_inv_sqrt_sub_le M hM0
    have e : G (M + 1) = G M + psiS M * (1 / √(M : ℝ) - 1 / √((M + 1 : ℕ) : ℝ)) := by
      show tS (M + 1) - psiS (M + 1) / √((M + 1 : ℕ) : ℝ) =
        tS M - psiS M / √(M : ℝ) + psiS M * (1 / √(M : ℝ) - 1 / √((M + 1 : ℕ) : ℝ))
      rw [tS_succ, psiS_succ]
      ring
    rw [e]
    have h1 : psiS M * (1 / √(M : ℝ) - 1 / √((M + 1 : ℕ) : ℝ)) ≤
        1.0004 * M * (1 / √(M : ℝ) - 1 / √((M + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hpsi hfac
    nlinarith
  have hind : ∀ M : ℕ, 2000000 ≤ M → G M ≤ G 2000000 + 1.0004 * (√(M : ℝ) - √(2000000 : ℝ)) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      have := hstep M hM
      push_cast at this ⊢
      linarith
  have hB := bS_N0
  have hGN := hind N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsq : psiS N / √(N : ℝ) ≤ 1.0004 * √(N : ℝ) := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hN')]
    have := h14 N hN
    have e : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN'.le
    nlinarith
  have : tS N = G N + psiS N / √(N : ℝ) := by show tS N = tS N - psiS N / √(N : ℝ) + _; ring
  rw [this]
  linarith

/-- **[H, (2.18)]** for `y ≥ 1`, given (2.14) for `y ≥ 2·10⁶`. -/
theorem sum_vonMangoldt_div_sqrt_lt_of
    (h14 : ∀ y : ℝ, 2e6 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y)
    {y : ℝ} (hy : 1 ≤ y) : ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / √(n : ℝ) < 2 * 1.0004 * √y := by
  rcases lt_or_ge y 2000001 with h | h
  · exact sum_vonMangoldt_div_sqrt_lt_small hy h
  · have hy0 : 0 ≤ y := by linarith
    have hm : 2000000 ≤ ⌊y⌋₊ := Nat.le_floor (by push_cast; linarith)
    have h14' : ∀ N : ℕ, 2000000 ≤ N → psiS N ≤ 1.0004 * N := by
      intro N hN
      have := h14 N (by norm_num; exact_mod_cast hN)
      rwa [Nat.floor_natCast] at this
    have := tS_lt_of_psi h14' hm
    have hsy : √(⌊y⌋₊ : ℝ) ≤ √y := Real.sqrt_le_sqrt (Nat.floor_le hy0)
    change tS ⌊y⌋₊ < _
    linarith

/-! ### (2.19) -/

/-- **[H, (2.19)]** for `117 ≤ y < 2·10⁶ + 1`, unconditionally (stated as
`TernaryGoldbach.Prelim.sum_log_sq_primes_le`). -/
theorem sum_log_sq_primes_le_small {y : ℝ} (h1 : 117 ≤ y) (h2 : y < 2000001) :
    ∑ p ∈ (Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y := by
  have hy0 : 0 ≤ y := by linarith
  set N := ⌊y⌋₊ with hNdef
  have hm1 : 117 ≤ N := Nat.le_floor (by exact_mod_cast h1)
  have hm2 : N ≤ 2000000 := by
    have := Nat.floor_lt hy0 |>.mpr (show y < ((2000001 : ℕ) : ℝ) by exact_mod_cast h2)
    omega
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsub : (Ioc ⌊y / 2⌋₊ N).filter Nat.Prime ⊆ (Ioc (N / 2) N).filter Nat.Prime := by
    apply filter_subset_filter
    apply Ioc_subset_Ioc_left
    apply Nat.le_floor
    have : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
    linarith
  have hmono := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg (Real.log p))
  have hgood := (goodAt N (by omega) hm2).2.2 hm1
  have hrhs : 1 / 2 * (N : ℝ) * Real.log N ≤ 1 / 2 * y * Real.log y := by
    have h1' : Real.log N ≤ Real.log y := Real.log_le_log hN0 hNy
    have h2' : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have := mul_le_mul hNy h1' h2' (by linarith)
    nlinarith
  linarith

/-- **[H, (2.19)]** for `y ≥ 117`, given it for `y ≥ 2·10⁶`. -/
theorem sum_log_sq_primes_le_of
    (hbig : ∀ y : ℝ, 2e6 ≤ y →
      ∑ p ∈ (Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y)
    {y : ℝ} (hy : 117 ≤ y) :
    ∑ p ∈ (Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y := by
  rcases lt_or_ge y 2000001 with h | h
  · exact sum_log_sq_primes_le_small hy h
  · exact hbig y (by norm_num; linarith)

end RSBounds.HelfgottLow
