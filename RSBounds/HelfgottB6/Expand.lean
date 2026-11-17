import RSBounds.HelfgottB6.Grid

/-!
# (B.6) with `31.521`: `K` integrations by parts

With `w = 1/(2πt)`, `E(u) = e(−ut)` and `Jₙ(a, b) = ∫_a^b E(u) u⁻ⁿ du`, one integration by parts
gives `Jₙ = iw [E u⁻ⁿ]_a^b + n iw Jₙ₊₁` (`Jn_succ`), so

`J₂(a, b) = ∑_{j<K} (iw)^{j+1} (j+1)! [E u^{−(j+2)}]_a^b + (iw)ᴷ (K+1)! J_{K+2}(a, b)`

(`Jn_two_expand`), with `‖J_{K+2}‖ ≤ (a^{−(K+1)} − b^{−(K+1)})/(K+1)` (`norm_Jn_le`). Since
`eta2DD t = 16z² − 16z − 4z⁴ + 4J₂(1/4, 1/2) − 4J₂(1/2, 1)` with `z = e(−t/4)`, this gives

`eta2DD t = Φ₁(w) z + Φ₂(w) z² + Φ₄(w) z⁴ + O*(4 K! (4^{K+1} − 1) wᴷ)`

(`norm_eta2DD_sub_FK`), where `Φₖ` are the polynomials of degree `K` whose coefficients are
`f1`, `f2`, `f4` (`RSBounds.HelfgottB6.Grid`).
-/

open Real Complex MeasureTheory Finset

namespace RSBounds.HelfgottB6

open TernaryGoldbach TernaryGoldbach.MinorArcs

/-- `Jₙ(a, b) = ∫_a^b e(−ut) u⁻ⁿ du`. -/
noncomputable def Jn (a b t : ℝ) (n : ℕ) : ℂ := ∫ u in a..b, e (-(u * t)) * (((u ^ n)⁻¹ : ℝ) : ℂ)

theorem hasDerivAt_inv_pow_nat (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => (u ^ n)⁻¹) (-(n : ℝ) * (x ^ (n + 1))⁻¹) x := by
  have h := (hasDerivAt_pow n x).inv (pow_ne_zero n hx)
  convert h using 1
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

theorem pos_of_mem_uIcc {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : x ∈ Set.uIcc a b) : 0 < x := by
  rw [Set.uIcc_of_le hab] at hx; exact ha.trans_le hx.1

/-- **One integration by parts**: `Jₙ = iw ([E u⁻ⁿ]_a^b + n Jₙ₊₁)`. -/
theorem Jn_succ {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) (n : ℕ) :
    Jn a b t n = (I * ((1 / (2 * π * t) : ℝ) : ℂ)) *
      ((e (-(b * t)) * (((b ^ n)⁻¹ : ℝ) : ℂ) - e (-(a * t)) * (((a ^ n)⁻¹ : ℝ) : ℂ)) +
        (n : ℂ) * Jn a b t (n + 1)) := by
  set w : ℝ := 1 / (2 * π * t)
  have hcw : -(2 * π * I * t) * (I * (w : ℂ)) = 1 := I_w_mul_c ht
  have hd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => (u ^ n)⁻¹) (-(n : ℝ) * (x ^ (n + 1))⁻¹) x :=
    fun x hx => hasDerivAt_inv_pow_nat n (pos_of_mem_uIcc ha hab hx).ne'
  have h : (-(2 * π * I * t)) * Jn a b t n =
      (e (-(b * t)) * (((b ^ n)⁻¹ : ℝ) : ℂ) - e (-(a * t)) * (((a ^ n)⁻¹ : ℝ) : ℂ)) -
        ∫ u in a..b, e (-(u * t)) * (((-(n : ℝ) * (u ^ (n + 1))⁻¹ : ℝ)) : ℂ) :=
    ibp1 hd (continuousOn_inv_pow ha hab (-(n : ℝ)) (n + 1))
  have h2 : ∫ u in a..b, e (-(u * t)) * (((-(n : ℝ) * (u ^ (n + 1))⁻¹ : ℝ)) : ℂ) =
      -(n : ℂ) * Jn a b t (n + 1) := by
    unfold Jn
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext u; push_cast; ring
  rw [h2] at h
  have h3 : Jn a b t n = (I * (w : ℂ)) * ((-(2 * π * I * t)) * Jn a b t n) := by
    rw [← mul_assoc, mul_comm (I * (w : ℂ)), hcw, one_mul]
  rw [h3, h]
  ring

/-- **`K` integrations by parts** of `J₂(a, b) = ∫_a^b e(−ut) u⁻² du`. -/
theorem Jn_two_expand {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ≠ 0) (K : ℕ) :
    Jn a b t 2 = ∑ j ∈ range K, (I * ((1 / (2 * π * t) : ℝ) : ℂ)) ^ (j + 1) *
        ((j + 1).factorial : ℂ) *
        (e (-(b * t)) * (((b ^ (j + 2))⁻¹ : ℝ) : ℂ) - e (-(a * t)) * (((a ^ (j + 2))⁻¹ : ℝ) : ℂ)) +
      (I * ((1 / (2 * π * t) : ℝ) : ℂ)) ^ K * ((K + 1).factorial : ℂ) * Jn a b t (K + 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, Jn_succ ha hab ht (K + 2), sum_range_succ, Nat.factorial_succ (K + 1),
      show K + 1 + 2 = K + 2 + 1 from rfl]
    push_cast
    ring

/-- `‖J_{n+2}(a, b)‖ ≤ (a^{−(n+1)} − b^{−(n+1)})/(n + 1)`. -/
theorem norm_Jn_le {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    ‖Jn a b t (n + 2)‖ ≤ ((a ^ (n + 1))⁻¹ - (b ^ (n + 1))⁻¹) / ((n : ℝ) + 1) := by
  have hG : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -(u ^ (n + 1))⁻¹ / ((n : ℝ) + 1))
      ((fun u : ℝ => (u ^ (n + 2))⁻¹) x) x := by
    intro x hx
    have hx0 := (pos_of_mem_uIcc ha hab hx).ne'
    have := ((hasDerivAt_inv_pow_nat (n + 1) hx0).neg).div_const ((n : ℝ) + 1)
    convert this using 1
    push_cast
    field_simp
  have hc : ContinuousOn (fun u : ℝ => (u ^ (n + 2))⁻¹) (Set.uIcc a b) := by
    simpa using continuousOn_inv_pow ha hab 1 (n + 2)
  have h : ‖Jn a b t (n + 2)‖ ≤ _ := norm_integral_E_le (t := t) hab hG hc fun x hx => by
    have : 0 < x := ha.trans_le hx.1
    positivity
  refine h.trans (le_of_eq ?_)
  ring

/-! ## The polynomials `Φₖ` -/

theorem toC_ipowQ (n : ℕ) : toC (ipowQ n) = I ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [ipowQ, toC]
  | succ n ih =>
    rw [ipowQ, toC_cmul, ih, pow_succ]
    congr 1
    apply Complex.ext <;> simp [toC]

theorem toC_cQ_zero (b : ℚ) (r : ℕ → ℚ) : toC (cQ b r 0) = (b : ℂ) := by
  apply Complex.ext <;> simp [cQ, toC]

theorem toC_cQ_succ (b : ℚ) (r : ℕ → ℚ) (n : ℕ) :
    toC (cQ b r (n + 1)) = 4 * ((n + 1).factorial : ℂ) * (r (n + 1) : ℂ) * I ^ (n + 1) := by
  rw [cQ, toC_smulQ, toC_ipowQ]
  push_cast
  ring

/-- `∑_{n<L} fₙ wⁿ` over `ℂ`. -/
noncomputable def polyC (f : ℕ → ℚ × ℚ) (L : ℕ) (w : ℝ) : ℂ :=
  ∑ n ∈ range L, toC (f n) * (w : ℂ) ^ n

/-- `F_K(z, w) = Φ₁(w) z + Φ₂(w) z² + Φ₄(w) z⁴`, `Φₖ` of degree `K`. -/
noncomputable def FK (K : ℕ) (z : ℂ) (w : ℝ) : ℂ :=
  polyC f1 (K + 1) w * z + polyC f2 (K + 1) w * z ^ 2 + polyC f4 (K + 1) w * z ^ 4

/-- The remainder after `K` integrations by parts: `4 K! (4^{K+1} − 1) wᴷ`. -/
noncomputable def RK (K : ℕ) (w : ℝ) : ℝ := 4 * (K.factorial : ℝ) * (4 ^ (K + 1) - 1) * w ^ K

theorem main_eq (K : ℕ) (z : ℂ) (w : ℝ) :
    16 * z ^ 2 - 16 * z - 4 * z ^ 4 +
      4 * ∑ j ∈ range K, (I * (w : ℂ)) ^ (j + 1) * ((j + 1).factorial : ℂ) *
        (z ^ 2 * (((((1 : ℝ) / 2) ^ (j + 2))⁻¹ : ℝ) : ℂ) -
          z * (((((1 : ℝ) / 4) ^ (j + 2))⁻¹ : ℝ) : ℂ)) -
      4 * ∑ j ∈ range K, (I * (w : ℂ)) ^ (j + 1) * ((j + 1).factorial : ℂ) *
        (z ^ 4 * ((((1 : ℝ) ^ (j + 2))⁻¹ : ℝ) : ℂ) -
          z ^ 2 * (((((1 : ℝ) / 2) ^ (j + 2))⁻¹ : ℝ) : ℂ)) =
    FK K z w := by
  have key : ∀ j ∈ range K,
      4 * ((I * (w : ℂ)) ^ (j + 1) * ((j + 1).factorial : ℂ) *
        (z ^ 2 * (((((1 : ℝ) / 2) ^ (j + 2))⁻¹ : ℝ) : ℂ) -
          z * (((((1 : ℝ) / 4) ^ (j + 2))⁻¹ : ℝ) : ℂ))) -
      4 * ((I * (w : ℂ)) ^ (j + 1) * ((j + 1).factorial : ℂ) *
        (z ^ 4 * ((((1 : ℝ) ^ (j + 2))⁻¹ : ℝ) : ℂ) -
          z ^ 2 * (((((1 : ℝ) / 2) ^ (j + 2))⁻¹ : ℝ) : ℂ))) =
      toC (f1 (j + 1)) * (w : ℂ) ^ (j + 1) * z + toC (f2 (j + 1)) * (w : ℂ) ^ (j + 1) * z ^ 2 +
        toC (f4 (j + 1)) * (w : ℂ) ^ (j + 1) * z ^ 4 := by
    intro j _
    simp only [f1, f2, f4, toC_cQ_succ, r1, r2, r4, one_div, inv_pow, inv_inv, one_pow, inv_one]
    push_cast
    ring
  calc _ = (16 * z ^ 2 - 16 * z - 4 * z ^ 4) + ∑ j ∈ range K,
        (4 * ((I * (w : ℂ)) ^ (j + 1) * ((j + 1).factorial : ℂ) *
          (z ^ 2 * (((((1 : ℝ) / 2) ^ (j + 2))⁻¹ : ℝ) : ℂ) -
            z * (((((1 : ℝ) / 4) ^ (j + 2))⁻¹ : ℝ) : ℂ))) -
        4 * ((I * (w : ℂ)) ^ (j + 1) * ((j + 1).factorial : ℂ) *
          (z ^ 4 * ((((1 : ℝ) ^ (j + 2))⁻¹ : ℝ) : ℂ) -
            z ^ 2 * (((((1 : ℝ) / 2) ^ (j + 2))⁻¹ : ℝ) : ℂ)))) := by
        simp only [Finset.sum_sub_distrib, Finset.mul_sum]
        ring
    _ = (16 * z ^ 2 - 16 * z - 4 * z ^ 4) + ∑ j ∈ range K,
        (toC (f1 (j + 1)) * (w : ℂ) ^ (j + 1) * z + toC (f2 (j + 1)) * (w : ℂ) ^ (j + 1) * z ^ 2 +
          toC (f4 (j + 1)) * (w : ℂ) ^ (j + 1) * z ^ 4) := by
        rw [Finset.sum_congr rfl key]
    _ = FK K z w := by
        unfold FK polyC
        rw [sum_range_succ', sum_range_succ', sum_range_succ']
        simp only [Finset.sum_add_distrib, add_mul, Finset.sum_mul, f1, f2, f4, toC_cQ_zero,
          pow_zero, mul_one]
        push_cast
        ring

/-- **`eta2DD t = F_K(e(−t/4), 1/(2πt)) + O*(4 K! (4^{K+1} − 1) wᴷ)`** for `t > 0`. -/
theorem norm_eta2DD_sub_FK {t : ℝ} (ht : 0 < t) (K : ℕ) :
    ‖eta2DD t - FK K (e (-(1 / 4 * t))) (1 / (2 * π * t))‖ ≤ RK K (1 / (2 * π * t)) := by
  set w : ℝ := 1 / (2 * π * t) with hw
  have hw0 : 0 < w := by positivity
  set z := e (-(1 / 4 * t))
  have e2 : e (-(1 / 2 * t)) = z ^ 2 := by
    rw [sq, ← e_add]; congr 1; ring
  have e4 : e (-(1 * t)) = z ^ 4 := by
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, ← e2, sq, ← e_add]; congr 1; ring
  have h1 := Jn_two_expand (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num) ht.ne' K
  have h2 := Jn_two_expand (a := 1 / 2) (b := 1) (by norm_num) (by norm_num) ht.ne' K
  rw [← hw] at h1 h2
  set R1 := (I * (w : ℂ)) ^ K * ((K + 1).factorial : ℂ) * Jn (1 / 4) (1 / 2) t (K + 2)
  set R2 := (I * (w : ℂ)) ^ K * ((K + 1).factorial : ℂ) * Jn (1 / 2) 1 t (K + 2)
  have hE : eta2DD t - FK K z w = 4 * R1 - 4 * R2 := by
    have hJ1 : Jq (1 / 4) (1 / 2) t = Jn (1 / 4) (1 / 2) t 2 := rfl
    have hJ2 : Jq (1 / 2) 1 t = Jn (1 / 2) 1 t 2 := rfl
    rw [← main_eq K z w, eta2DD, hJ1, hJ2, h1, h2, e2, e4]
    ring
  have hR : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ‖(I * (w : ℂ)) ^ K * ((K + 1).factorial : ℂ) * Jn a b t (K + 2)‖ ≤
        w ^ K * (K.factorial : ℝ) * ((a ^ (K + 1))⁻¹ - (b ^ (K + 1))⁻¹) := by
    intro a b ha hab
    rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hw0, Complex.norm_natCast]
    have hJ := norm_Jn_le (t := t) ha hab K
    have hK : ((K + 1).factorial : ℝ) = ((K : ℝ) + 1) * K.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hK]
    calc w ^ K * (((K : ℝ) + 1) * K.factorial) * ‖Jn a b t (K + 2)‖
        ≤ w ^ K * (((K : ℝ) + 1) * K.factorial) *
            (((a ^ (K + 1))⁻¹ - (b ^ (K + 1))⁻¹) / ((K : ℝ) + 1)) := by gcongr
      _ = w ^ K * (K.factorial : ℝ) * ((a ^ (K + 1))⁻¹ - (b ^ (K + 1))⁻¹) := by
        field_simp
  have hR1 := hR (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num)
  have hR2 := hR (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)
  rw [hE]
  calc ‖4 * R1 - 4 * R2‖ ≤ 4 * ‖R1‖ + 4 * ‖R2‖ := by
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul]; norm_num
    _ ≤ 4 * (w ^ K * (K.factorial : ℝ) * ((((1 : ℝ) / 4) ^ (K + 1))⁻¹ - (((1 : ℝ) / 2) ^ (K + 1))⁻¹)) +
        4 * (w ^ K * (K.factorial : ℝ) * ((((1 : ℝ) / 2) ^ (K + 1))⁻¹ - ((1 : ℝ) ^ (K + 1))⁻¹)) := by
        gcongr
    _ = RK K w := by
        unfold RK
        simp only [one_div, inv_pow, inv_inv, one_pow, inv_one]
        ring

end RSBounds.HelfgottB6
