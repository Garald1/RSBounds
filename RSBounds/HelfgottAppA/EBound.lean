import RSBounds.HelfgottAppA.NonPrime

/-!
# [H] (14.28) with Helfgott's constant `8.4029·10⁻¹²`

[H] = H. A. Helfgott, *The ternary Goldbach problem*, arXiv:1501.05438v2. In Thm 13.2.1 (as used
in §14.4),
`E = ∑_{n non-prime or n ≤ √x} Λ(n)² η₊(n/x)²`, and [H, (14.28)] states
`E ≤ (2.94325 log x + 5.12426) √x ≤ 8.4029·10⁻¹² x` for `x ≥ 4.9·10²⁶`.

[H, §13.2]'s argument: the terms with `n ≤ √x` contribute at most
`|η₊|²_∞ (log x/2) ψ(√x) ≤ 0.51942 |η₊|²_∞ √x log x`; for the non-prime terms, with a non-increasing
majorant `F(t) ≥ η₊(t/x)²` and `∑_{n ≤ t, n non-prime} Λ(n)² ≤ B(t) = 1.4262 √t log t`, summation
by parts gives `∑ Λ(n)² F(n) ≤ ∫_1^∞ B'(t) F(t) dt`. Here `F(t) = min(1.079955, 1.19073 x/t)²`,
from [H, (14.3)] and (14.24) (`EtaPlusSup.lean`), and the integral is computed in closed form on
`[1, x]` and `[x, ∞)`. This gives `E ≤ (2.94323 log x + 1.79748) √x`, slightly better than [H]
(whose constant term comes from a cruder split), hence (14.28) as stated (`E_le_14_28_book`,
`E_le_book_formula`).

The sum `E` is written as in calr3/ternary-goldbach's `E_le_14_28`. The inputs
`ψ(n) ≤ 1.03883 n` and `ψ(y) − θ(y) < 1.4262 √y` ([RS62, Thms 12, 13]) are hypotheses, `hpsi` and
`h55`, stated as calr3 proves them from `PlattGRH` (`Prelim.psi_bounds`,
`Prelim.sum_vonMangoldt_nonprime_lt`).
-/

open Real Finset
open scoped ArithmeticFunction.vonMangoldt

namespace RSBounds.HelfgottAppA

open TernaryGoldbach.Helfgott (etaPlus)

/-! ## Summation by parts -/

/-- If the partial sums of `a` are at most those of `b` and `F ≥ 0` is non-increasing on `n ≥ 1`,
then `∑ a F ≤ ∑ b F`. -/
theorem sum_mul_le_of_partial {a b F : ℕ → ℝ} (M : ℕ) (hF : ∀ n, 1 ≤ n → F (n + 1) ≤ F n)
    (hF0 : ∀ n, 0 ≤ F n) (hD : ∀ n ≤ M, ∑ k ∈ Icc 1 n, a k ≤ ∑ k ∈ Icc 1 n, b k) :
    ∑ n ∈ Icc 1 M, a n * F n ≤ ∑ n ∈ Icc 1 M, b n * F n := by
  have key : ∀ m ≤ M, (∑ k ∈ Icc 1 m, (b k - a k)) * F m ≤ ∑ k ∈ Icc 1 m, (b k - a k) * F k := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
      have hDm : 0 ≤ ∑ k ∈ Icc 1 m, (b k - a k) := by
        rw [sum_sub_distrib]; linarith [hD m (by omega)]
      have hmono : (∑ k ∈ Icc 1 m, (b k - a k)) * F (m + 1) ≤ (∑ k ∈ Icc 1 m, (b k - a k)) * F m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · subst h0; simp
        · exact mul_le_mul_of_nonneg_left (hF m hpos) hDm
      nlinarith
  have h := key M le_rfl
  have hD0 : 0 ≤ ∑ k ∈ Icc 1 M, (b k - a k) := by rw [sum_sub_distrib]; linarith [hD M le_rfl]
  have : 0 ≤ ∑ k ∈ Icc 1 M, (b k - a k) * F k := le_trans (mul_nonneg hD0 (hF0 M)) h
  have e : ∑ k ∈ Icc 1 M, (b k - a k) * F k = ∑ k ∈ Icc 1 M, b k * F k - ∑ k ∈ Icc 1 M, a k * F k := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun k _ => by ring
  linarith

/-! ## `B(t) = 1.4262 √t log t` -/

/-- `B(t) = 1.4262 √t log t`. -/
noncomputable def Bf (t : ℝ) : ℝ := 1.4262 * √t * Real.log t

/-- `B'(t) = 0.7131 (2 + log t)/√t`. -/
noncomputable def Bf' (t : ℝ) : ℝ := 0.7131 * (2 + Real.log t) / √t

theorem hasDerivAt_Bf {t : ℝ} (ht : 0 < t) : HasDerivAt Bf (Bf' t) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hl := Real.hasDerivAt_log ht.ne'
  have h := (hs.const_mul 1.4262).mul hl
  have e : Bf' t = 1.4262 * (1 / (2 * √t)) * Real.log t + 1.4262 * √t * t⁻¹ := by
    obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ t = u ^ 2 :=
      ⟨√t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
    unfold Bf'
    rw [Real.sqrt_sq hu.le]
    field_simp
    ring
  rw [e]
  exact h

theorem Bf_zero : Bf 0 = 0 := by simp [Bf]

theorem Bf_one : Bf 1 = 0 := by simp [Bf]

theorem Bf'_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ Bf' t := by
  unfold Bf'
  have := Real.log_nonneg ht
  positivity

theorem continuousOn_Bf' : ContinuousOn Bf' (Set.Ioi 0) := by
  intro t ht
  have ht' : (0:ℝ) < t := ht
  unfold Bf'
  refine ContinuousAt.continuousWithinAt ?_
  refine ((continuousAt_const.mul (continuousAt_const.add (Real.continuousAt_log ht'.ne')))).div
    (Real.continuous_sqrt.continuousAt) (Real.sqrt_pos.2 ht').ne'

theorem integral_Bf' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ∫ t in a..b, Bf' t = Bf b - Bf a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_Bf ?_) ?_
  · rw [Set.uIcc_of_le hab] at ht; exact ha.trans_le ht.1
  · refine (continuousOn_Bf'.mono fun t ht => ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab] at ht; exact ha.trans_le ht.1

/-! ## The majorant `F` -/

/-- `A = 1.079955 ≥ |η₊|_∞` and `B = 1.19073 ≥ |η₊ · t|_∞`. -/
noncomputable def Fm (x t : ℝ) : ℝ := (min 1.079955 (1.19073 * x / t)) ^ 2

theorem Fm_nonneg (x t : ℝ) : 0 ≤ Fm x t := sq_nonneg _

theorem min_nonneg' {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) : 0 ≤ min 1.079955 (1.19073 * x / t) :=
  le_min (by norm_num) (by positivity)

theorem Fm_antitone {x s t : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (hst : s ≤ t) : Fm x t ≤ Fm x s := by
  unfold Fm
  have h1 : min 1.079955 (1.19073 * x / t) ≤ min 1.079955 (1.19073 * x / s) :=
    min_le_min le_rfl (div_le_div_of_nonneg_left (by positivity) hs hst)
  exact pow_le_pow_left₀ (min_nonneg' hx (hs.le.trans hst)) h1 2

theorem Fm_le_A {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) : Fm x t ≤ 1.079955 ^ 2 :=
  pow_le_pow_left₀ (min_nonneg' hx ht) (min_le_left _ _) 2

theorem Fm_le_B {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) : Fm x t ≤ (1.19073 * x / t) ^ 2 :=
  pow_le_pow_left₀ (min_nonneg' hx ht) (min_le_right _ _) 2

theorem etaPlus_sq_le_Fm {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) : etaPlus (n / x) ^ 2 ≤ Fm x n := by
  have hu : 0 < (n : ℝ) / x := div_pos (by exact_mod_cast hn) hx
  have h1 := abs_etaPlus_le_1079955 hu.le
  have h2 := mul_abs_etaPlus_le_119073 hu.le
  have h3 : |etaPlus (n / x)| ≤ 1.19073 * x / n := by
    rw [le_div_iff₀ (by exact_mod_cast hn : (0:ℝ) < n)]
    have : (n : ℝ) / x * |etaPlus (n / x)| * x = n * |etaPlus (n / x)| := by field_simp
    nlinarith
  unfold Fm
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (le_min h1 h3) 2

theorem antitoneOn_Fm {x : ℝ} (hx : 0 ≤ x) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    AntitoneOn (Fm x) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  intro s hs t _ hst
  exact Fm_antitone hx (ha.trans_le hs.1) hst

theorem intervalIntegrable_Bf'_Fm {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Bf' t * Fm x t) MeasureTheory.volume a b := by
  have h1 : IntervalIntegrable (Fm x) MeasureTheory.volume a b :=
    (antitoneOn_Fm hx ha hab).intervalIntegrable
  have h2 : ContinuousOn Bf' (Set.uIcc a b) := continuousOn_Bf'.mono fun t ht => by
    rw [Set.uIcc_of_le hab] at ht; exact ha.trans_le ht.1
  have := h1.continuousOn_mul h2
  simpa only [mul_comm] using this

/-- `∑_{n=1}^M (B(n) − B(n − 1)) F(n) ≤ ∫_1^M B' F`. -/
theorem sum_le_integral {x : ℝ} (hx : 0 ≤ x) : ∀ M : ℕ, 1 ≤ M →
    ∑ n ∈ Icc 1 M, (Bf n - Bf (n - 1)) * Fm x n ≤ ∫ t in (1:ℝ)..M, Bf' t * Fm x t := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp [Bf_one, Bf_zero]
  | succ M hM ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hstep : (Bf ((M + 1 : ℕ) : ℝ) - Bf ((M + 1 : ℕ) - 1 : ℝ)) * Fm x ((M + 1 : ℕ) : ℝ) ≤
        ∫ t in (M : ℝ)..((M + 1 : ℕ) : ℝ), Bf' t * Fm x t := by
      have e : ((M + 1 : ℕ) : ℝ) - 1 = M := by push_cast; ring
      rw [e, ← integral_Bf' (by linarith) (by push_cast; linarith), ← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_mono_on (by push_cast; linarith)
        ((continuousOn_Bf'.mono fun t ht => by
          rw [Set.uIcc_of_le (by push_cast; linarith)] at ht
          exact (show (0:ℝ) < t from by linarith [ht.1])).intervalIntegrable.mul_const _)
        (intervalIntegrable_Bf'_Fm hx (by linarith) (by push_cast; linarith)) fun t ht => ?_
      have ht1 : 1 ≤ t := by linarith [ht.1]
      exact mul_le_mul_of_nonneg_left (Fm_antitone hx (by linarith) ht.2) (Bf'_nonneg ht1)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_Bf'_Fm hx (a := 1) (b := M) one_pos hM1)
      (intervalIntegrable_Bf'_Fm hx (a := M) (b := ((M + 1 : ℕ) : ℝ)) (by linarith) (by push_cast; linarith))
    rw [← hadd]
    linarith

/-! ## The integral -/

/-- `Γ(t) = −0.7131 (16/9 + (2/3) log t)/(t √t)`, an antiderivative of `B'(t)/t²`. -/
noncomputable def Gam (t : ℝ) : ℝ := -(0.7131 * (16 / 9 + 2 / 3 * Real.log t) / (t * √t))

theorem hasDerivAt_Gam {t : ℝ} (ht : 0 < t) : HasDerivAt Gam (Bf' t / t ^ 2) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hl := Real.hasDerivAt_log ht.ne'
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hden : HasDerivAt (fun t => t * √t) (1 * √t + t * (1 / (2 * √t))) t := (hasDerivAt_id t).mul hs
  have hnum : HasDerivAt (fun t => 0.7131 * (16 / 9 + 2 / 3 * Real.log t)) (0.7131 * (2 / 3 * t⁻¹)) t :=
    ((hl.const_mul (2 / 3)).const_add (16 / 9)).const_mul 0.7131
  have h := (hnum.div hden (mul_pos ht hst).ne').neg
  have e : Bf' t / t ^ 2 = -((0.7131 * (2 / 3 * t⁻¹) * (t * √t) - 0.7131 * (16 / 9 + 2 / 3 * Real.log t) *
      (1 * √t + t * (1 / (2 * √t)))) / (t * √t) ^ 2) := by
    obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ t = u ^ 2 :=
      ⟨√t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
    unfold Bf'
    rw [Real.sqrt_sq hu.le]
    field_simp
    ring
  rw [e]
  exact h

/-- `∫_1^M B' F ≤ A² B(x) + 0.7131 B² √x (16/9 + (2/3) log x)` for `M ≥ x ≥ 1`. -/
theorem integral_le {x : ℝ} (hx : 1 ≤ x) {M : ℝ} (hM : x ≤ M) :
    ∫ t in (1:ℝ)..M, Bf' t * Fm x t ≤
      1.079955 ^ 2 * Bf x + 0.7131 * 1.19073 ^ 2 * √x * (16 / 9 + 2 / 3 * Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_Bf'_Fm hx0 one_pos hx) (intervalIntegrable_Bf'_Fm hx0 (by linarith) hM)]
  have h1 : ∫ t in (1:ℝ)..x, Bf' t * Fm x t ≤ 1.079955 ^ 2 * Bf x := by
    have : ∫ t in (1:ℝ)..x, Bf' t * Fm x t ≤ ∫ t in (1:ℝ)..x, Bf' t * 1.079955 ^ 2 := by
      refine intervalIntegral.integral_mono_on hx (intervalIntegrable_Bf'_Fm hx0 one_pos hx)
        ((continuousOn_Bf'.mono fun t ht => by
          rw [Set.uIcc_of_le hx] at ht; exact (show (0:ℝ) < t by linarith [ht.1])).intervalIntegrable.mul_const _)
        fun t ht => mul_le_mul_of_nonneg_left (Fm_le_A hx0 (by linarith [ht.1])) (Bf'_nonneg ht.1)
    rw [intervalIntegral.integral_mul_const, integral_Bf' one_pos hx, Bf_one, sub_zero] at this
    linarith
  have h2 : ∫ t in x..M, Bf' t * Fm x t ≤ 0.7131 * 1.19073 ^ 2 * √x * (16 / 9 + 2 / 3 * Real.log x) := by
    have hcont : ContinuousOn (fun t => Bf' t / t ^ 2) (Set.uIcc x M) := by
      rw [Set.uIcc_of_le hM]
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      exact ((continuousOn_Bf' t ht0).div (continuousWithinAt_id.pow 2) (pow_pos ht0 2).ne').mono
        (fun s hs => (show (0:ℝ) < s by linarith [hs.1]))
    have : ∫ t in x..M, Bf' t * Fm x t ≤ ∫ t in x..M, (1.19073 * x) ^ 2 * (Bf' t / t ^ 2) := by
      refine intervalIntegral.integral_mono_on hM (intervalIntegrable_Bf'_Fm hx0 (by linarith) hM)
        (hcont.intervalIntegrable.const_mul _) fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      have hb := Fm_le_B hx0 ht0.le
      calc Bf' t * Fm x t ≤ Bf' t * (1.19073 * x / t) ^ 2 :=
            mul_le_mul_of_nonneg_left hb (Bf'_nonneg (by linarith [ht.1]))
        _ = (1.19073 * x) ^ 2 * (Bf' t / t ^ 2) := by field_simp
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_Gam (by rw [Set.uIcc_of_le hM] at ht; linarith [ht.1]))
      hcont.intervalIntegrable] at this
    have hGM : Gam M ≤ 0 := by
      unfold Gam
      have : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
      have : 0 < M := by linarith
      have : 0 < M * √M := by positivity
      have : 0 ≤ 0.7131 * (16 / 9 + 2 / 3 * Real.log M) / (M * √M) := by positivity
      linarith
    have hGx : -((1.19073 * x) ^ 2 * Gam x) = 0.7131 * 1.19073 ^ 2 * √x * (16 / 9 + 2 / 3 * Real.log x) := by
      obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ x = u ^ 2 :=
        ⟨√x, Real.sqrt_pos.2 (by linarith), (Real.sq_sqrt hx0).symm⟩
      unfold Gam
      rw [Real.sqrt_sq hu.le]
      field_simp
    have : (1.19073 * x) ^ 2 * Gam M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hGM
    linarith
  linarith

/-! ## The sum `E` -/

theorem sum_Bf_telescope : ∀ n : ℕ, ∑ k ∈ Icc 1 n, (Bf k - Bf ((k : ℝ) - 1)) = Bf n := by
  intro n
  induction n with
  | zero => simp [Bf_zero]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    have e : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
    rw [e]; ring

/-- `∑_{k ≤ n, k non-prime} Λ(k)² ≤ 1.4262 √n log n`. -/
theorem partial_nonprime_sq_le
    (h55 : ∀ y : ℝ, 0 < y → ∑ n ∈ Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    (n : ℕ) :
    ∑ k ∈ Icc 1 n, (if k.Prime then 0 else (Λ k : ℝ) ^ 2) ≤ Bf n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [Bf_zero]
  have hn : (0 : ℝ) < n := by exact_mod_cast hpos
  have h55 := h55 n hn
  rw [Nat.floor_natCast] at h55
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hterm : ∀ k ∈ Icc 1 n, (if k.Prime then 0 else (Λ k : ℝ) ^ 2) ≤
      Real.log n * (if k.Prime then 0 else (Λ k : ℝ)) := by
    intro k hk
    rw [mem_Icc] at hk
    split_ifs
    · simp
    · have h1 : (Λ k : ℝ) ≤ Real.log n := by
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        exact Real.log_le_log (by exact_mod_cast hk.1) (by exact_mod_cast hk.2)
      have h0 : (0 : ℝ) ≤ Λ k := ArithmeticFunction.vonMangoldt_nonneg
      nlinarith
  calc ∑ k ∈ Icc 1 n, (if k.Prime then 0 else (Λ k : ℝ) ^ 2)
      ≤ ∑ k ∈ Icc 1 n, Real.log n * (if k.Prime then 0 else (Λ k : ℝ)) := sum_le_sum hterm
    _ = Real.log n * ∑ k ∈ Icc 1 n, (if k.Prime then 0 else (Λ k : ℝ)) := by rw [mul_sum]
    _ ≤ Real.log n * (1.4262 * √(n : ℝ)) := mul_le_mul_of_nonneg_left h55.le hlog
    _ = Bf n := by unfold Bf; ring

/-- The non-prime part: `∑_{n ≤ M, n non-prime} Λ(n)² F(n) ≤ A² B(x) + 0.7131 B² √x (16/9 + (2/3) log x)`. -/
theorem E1_partial
    (h55 : ∀ y : ℝ, 0 < y → ∑ n ∈ Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    {x : ℝ} (hx : 1 ≤ x) (M : ℕ) :
    ∑ n ∈ Icc 1 M, (if n.Prime then 0 else (Λ n : ℝ) ^ 2) * Fm x n ≤
      1.079955 ^ 2 * Bf x + 0.7131 * 1.19073 ^ 2 * √x * (16 / 9 + 2 / 3 * Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  set M' := max M ⌈x⌉₊
  have hM' : M ≤ M' := le_max_left _ _
  have hxM' : x ≤ M' := (Nat.le_ceil x).trans (by exact_mod_cast le_max_right M ⌈x⌉₊)
  have hM'1 : 1 ≤ M' := by
    have : (1 : ℝ) ≤ M' := hx.trans hxM'
    exact_mod_cast this
  have hnn : ∀ n : ℕ, 0 ≤ (if n.Prime then 0 else (Λ n : ℝ) ^ 2) * Fm x n := fun n =>
    mul_nonneg (by split_ifs <;> positivity) (Fm_nonneg _ _)
  calc ∑ n ∈ Icc 1 M, (if n.Prime then 0 else (Λ n : ℝ) ^ 2) * Fm x n
      ≤ ∑ n ∈ Icc 1 M', (if n.Prime then 0 else (Λ n : ℝ) ^ 2) * Fm x n :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hM') fun n _ _ => hnn n
    _ ≤ ∑ n ∈ Icc 1 M', (Bf n - Bf ((n : ℝ) - 1)) * Fm x n := by
        refine sum_mul_le_of_partial (a := fun n => if n.Prime then 0 else (Λ n : ℝ) ^ 2)
          (b := fun n => Bf n - Bf ((n : ℝ) - 1)) (F := fun n => Fm x n) M'
          (fun n hn => Fm_antitone hx0 (by exact_mod_cast hn) (by push_cast; linarith))
          (fun n => Fm_nonneg _ _) fun n _ => ?_
        rw [sum_Bf_telescope]
        exact partial_nonprime_sq_le h55 n
    _ ≤ ∫ t in (1:ℝ)..M', Bf' t * Fm x t := sum_le_integral hx0 M' hM'1
    _ ≤ _ := integral_le hx hxM'

/-- One term of `E`, split into its non-prime and small parts. -/
theorem eTerm_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤
      (if n.Prime then 0 else (Λ n : ℝ) ^ 2) * Fm x n +
        (if (n : ℝ) ≤ √x then (Λ n : ℝ) ^ 2 * 1.079955 ^ 2 else 0) := by
  have h1 : 0 ≤ (if n.Prime then 0 else (Λ n : ℝ) ^ 2) * Fm x n :=
    mul_nonneg (by split_ifs <;> positivity) (Fm_nonneg _ _)
  have h2 : 0 ≤ (if (n : ℝ) ≤ √x then (Λ n : ℝ) ^ 2 * 1.079955 ^ 2 else 0) := by
    split_ifs <;> positivity
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  by_cases hA : n.Prime ∧ √x < n
  · rw [ite_eq_left hA]; exact add_nonneg h1 h2
  · rw [ite_eq_right hA, mul_pow]
    by_cases hP : n.Prime
    · have hS : (n : ℝ) ≤ √x := by
        by_contra h; exact hA ⟨hP, lt_of_not_ge h⟩
      rw [ite_eq_left hP, ite_eq_left hS, zero_mul, zero_add]
      have h4 := abs_etaPlus_le_1079955 (div_nonneg (Nat.cast_nonneg n) hx.le)
      have h5 : etaPlus (n / x) ^ 2 ≤ 1.079955 ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h4 2
      exact mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
    · rw [ite_eq_right hP]
      have h3 := mul_le_mul_of_nonneg_left (etaPlus_sq_le_Fm hx hpos) (sq_nonneg (Λ n : ℝ))
      linarith

/-- The small part: `∑_{n ≤ √x} Λ(n)² A² ≤ A² (log x/2) · 1.03883 √x`. -/
theorem E2_partial (hpsi : ∀ n : ℕ, ∑ m ∈ Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    {x : ℝ} (hx : 1 ≤ x) (M : ℕ) :
    ∑ n ∈ Icc 1 M, (if (n : ℝ) ≤ √x then (Λ n : ℝ) ^ 2 * 1.079955 ^ 2 else 0) ≤
      1.079955 ^ 2 * (Real.log x / 2 * (1.03883 * √x)) := by
  have hx0 : 0 < x := by linarith
  set K := ⌊√x⌋₊
  have hsub : ∀ n ∈ Icc 1 M, (if (n : ℝ) ≤ √x then (Λ n : ℝ) ^ 2 * 1.079955 ^ 2 else 0) ≤
      (if n ∈ Icc 1 K then 1.079955 ^ 2 * (Real.log x / 2 * (Λ n : ℝ)) else 0) := by
    intro n hn
    rw [mem_Icc] at hn
    split_ifs with h1 h2
    · rw [mem_Icc] at h2
      have hl : (Λ n : ℝ) ≤ Real.log x / 2 := by
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        have : Real.log n ≤ Real.log √x := Real.log_le_log (by exact_mod_cast hn.1) h1
        rwa [Real.log_sqrt hx0.le] at this
      have h0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      nlinarith
    · exact absurd (mem_Icc.2 ⟨hn.1, Nat.le_floor h1⟩) h2
    · have := Real.log_nonneg hx
      have : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      positivity
    · exact le_rfl
  have hK : ∑ n ∈ Icc 1 M, (if n ∈ Icc 1 K then 1.079955 ^ 2 * (Real.log x / 2 * (Λ n : ℝ)) else 0) ≤
      ∑ n ∈ Icc 1 K, 1.079955 ^ 2 * (Real.log x / 2 * (Λ n : ℝ)) := by
    rw [← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_filter.1 hn).2) fun n _ _ => ?_
    have := Real.log_nonneg hx
    have : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    positivity
  have hpsiK : ∑ m ∈ Icc 1 K, (Λ m : ℝ) ≤ 1.03883 * √x := by
    refine (hpsi K).trans ?_
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg x)) (by norm_num)
  have e : ∑ n ∈ Icc 1 K, 1.079955 ^ 2 * (Real.log x / 2 * (Λ n : ℝ)) =
      1.079955 ^ 2 * (Real.log x / 2 * ∑ m ∈ Icc 1 K, (Λ m : ℝ)) := by
    rw [mul_sum, mul_sum]
  have hl := Real.log_nonneg hx
  calc _ ≤ _ := sum_le_sum hsub
    _ ≤ _ := hK
    _ = _ := e
    _ ≤ _ := by gcongr

/-- `E ≤ (2.94325 log x + 1.8) √x` for `x ≥ 1`. -/
theorem E_le_sharp (hpsi : ∀ n : ℕ, ∑ m ∈ Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y → ∑ n ∈ Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤
      (2.94325 * Real.log x + 1.8) * √x := by
  have hx0 : 0 < x := by linarith
  have hnn : ∀ n : ℕ, 0 ≤ (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) := fun n => by
    split_ifs <;> positivity
  refine Real.tsum_le_of_sum_range_le hnn fun M => ?_
  have hr : range M ⊆ insert 0 (Icc 1 M) := by
    intro n hn; rw [mem_range] at hn; rw [mem_insert, mem_Icc]; omega
  have hz : (if (0 : ℕ).Prime ∧ √x < ((0 : ℕ) : ℝ) then 0 else (Λ 0 * etaPlus ((0 : ℕ) / x)) ^ 2) = (0 : ℝ) := by
    simp
  calc ∑ n ∈ range M, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2)
      ≤ ∑ n ∈ insert 0 (Icc 1 M), (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hr fun n _ _ => hnn n
    _ = ∑ n ∈ Icc 1 M, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) := by
        rw [sum_insert (by simp), hz, zero_add]
    _ ≤ ∑ n ∈ Icc 1 M, ((if n.Prime then 0 else (Λ n : ℝ) ^ 2) * Fm x n +
          (if (n : ℝ) ≤ √x then (Λ n : ℝ) ^ 2 * 1.079955 ^ 2 else 0)) :=
        sum_le_sum fun n _ => eTerm_le hx0 n
    _ = _ := sum_add_distrib
    _ ≤ (1.079955 ^ 2 * Bf x + 0.7131 * 1.19073 ^ 2 * √x * (16 / 9 + 2 / 3 * Real.log x)) +
          1.079955 ^ 2 * (Real.log x / 2 * (1.03883 * √x)) := add_le_add (E1_partial h55 hx M) (E2_partial hpsi hx M)
    _ ≤ (2.94325 * Real.log x + 1.8) * √x := by
        unfold Bf
        have hl := Real.log_nonneg hx
        have hs := Real.sqrt_nonneg x
        have : 0 ≤ Real.log x * √x := mul_nonneg hl hs
        nlinarith

/-- **[H, (14.28)]**, first form: `E ≤ (2.94325 log x + 5.12426) √x` for `x ≥ 1`. -/
theorem E_le_book_formula (hpsi : ∀ n : ℕ, ∑ m ∈ Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y → ∑ n ∈ Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤
      (2.94325 * Real.log x + 5.12426) * √x := by
  refine (E_le_sharp hpsi h55 hx).trans ?_
  have := Real.sqrt_nonneg x
  nlinarith

/-- **[H, (14.28)]**: `E ≤ 8.4029·10⁻¹² x` for `x ≥ 4.9·10²⁶`. -/
theorem E_le_14_28_book (hpsi : ∀ n : ℕ, ∑ m ∈ Icc 1 n, (Λ m : ℝ) ≤ 1.03883 * n)
    (h55 : ∀ y : ℝ, 0 < y → ∑ n ∈ Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y)
    {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤ 8.4029e-12 * x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  refine (E_le_sharp hpsi h55 hx1).trans ?_
  set s := √x with hs
  set L := Real.log x with hL
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hs13 : (2.2135e13 : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hL0 : 0 ≤ L := Real.log_nonneg hx1
  have hLs : L / s ≤ 61.5 / 2.2135e13 := by
    have he2 : Real.exp 2 ≤ (4.9e26 : ℝ) := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]; nlinarith [Real.exp_pos 1]
    have hanti := Real.log_div_sqrt_antitoneOn (Set.mem_Ici.2 he2) (Set.mem_Ici.2 (he2.trans hx)) hx
    simp only at hanti
    have hl : Real.log (4.9e26 : ℝ) ≤ 61.5 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 := Real.exp_one_gt_d9
      have h2 := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
      have e : Real.exp 61.5 = Real.exp 1 ^ 61 * Real.exp (1 / 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      have h3 : (2.7182818283 : ℝ) ^ 61 ≤ Real.exp 1 ^ 61 := pow_le_pow_left₀ (by norm_num) h1.le 61
      have h4 : (4.9e26 : ℝ) ≤ 2.7182818283 ^ 61 * 1.625 := by norm_num
      have h5 : (0 : ℝ) ≤ 2.7182818283 ^ 61 := by norm_num
      nlinarith
    have hsq : (2.2135e13 : ℝ) ≤ √(4.9e26 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
    refine hanti.trans ?_
    calc Real.log (4.9e26 : ℝ) / √(4.9e26 : ℝ) ≤ 61.5 / √(4.9e26 : ℝ) :=
          div_le_div_of_nonneg_right hl (Real.sqrt_nonneg _)
      _ ≤ 61.5 / 2.2135e13 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
  have hLs' : L ≤ 61.5 / 2.2135e13 * s := by rwa [div_le_iff₀ hs0] at hLs
  rw [← hss]
  nlinarith

end RSBounds.HelfgottAppA
