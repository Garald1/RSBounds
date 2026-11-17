import RSBounds.HelfgottB6.Expand

/-!
# (B.6) with `31.521`: soundness of the checks

**Region B** (`w = 1/(2πt) ∈ [0, 1/28]`). Write `z = s · zm(m)` (`s = ±1`, `m ∈ [−1, 1]`). On a cell
`[m₀, m₁] × [w₀, w₁]` with centre `(m_c, w_c)`, `zm(m) = zm(m_c) e^{iδ}` with `|δ| ≤ m₁ − m₀`
(`zm_eq_cexp`, `abs_arctan_sub_le`), and `Φₖ(w) = Φₖ(w_c) + d Φₖ'(w_c) + O*(C₂ d²)`, `d = w − w_c`
(`norm_polyC_taylor`). Expanding `e^{ikδ} = 1 + ikδ + O*((kδ)²)` gives
`F_K(z, w) = F₀ + iδ F_θ + d F_w + O*(E)` (`norm_F_le`), and
`|F₀ + iδF_θ + dF_w|² ≤ Q` (`quad_le`). The check `Q ≤ M²`, `M = 31.521 − R_K(w₁) − E ≥ 0`, then gives
`‖F_K(z, w)‖ + R_K(w) ≤ 31.521` on the whole cell (`cellB_sound`).

**Region A** (`x = 2πt ∈ [0, 28]`): as `TernaryGoldbach.MinorArcs.cellC_sound`, with `N = 90`,
`X = 28` and the bound `31.521` (`cellA_sound`).
-/

open Real Complex Finset

namespace RSBounds.HelfgottB6

open TernaryGoldbach TernaryGoldbach.MinorArcs

/-! ## Horner's rule and the derivative -/

theorem toC_hornQ (f : ℕ → ℚ × ℚ) (w : ℚ) :
    ∀ m i, toC (hornQ f w m i) = ∑ n ∈ range m, toC (f (i + n)) * ((w : ℝ) : ℂ) ^ n
  | 0, i => by apply Complex.ext <;> simp [hornQ, toC]
  | m + 1, i => by
    rw [hornQ, toC_cadd, toC_smulQ, toC_hornQ f w m (i + 1), sum_range_succ', mul_sum]
    simp only [add_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [show i + 1 + n = i + (n + 1) by ring]
    push_cast
    ring

theorem toC_hornQ_zero (f : ℕ → ℚ × ℚ) (w : ℚ) (L : ℕ) :
    toC (hornQ f w L 0) = polyC f L w := by
  rw [toC_hornQ]; simp [polyC]

/-- `Φ'(c) = ∑_{n<L} fₙ n c^{n−1}`. -/
noncomputable def DerC (f : ℕ → ℚ × ℚ) (L : ℕ) (c : ℝ) : ℂ :=
  ∑ n ∈ range L, toC (f n) * (n : ℂ) * (c : ℂ) ^ (n - 1)

theorem toC_hornQ_dQ (f : ℕ → ℚ × ℚ) (c : ℚ) (K : ℕ) :
    toC (hornQ (dQ f) c K 0) = DerC f (K + 1) c := by
  rw [toC_hornQ, DerC, sum_range_succ']
  simp only [zero_add, Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.add_sub_cancel]
  refine sum_congr rfl fun n _ => ?_
  rw [dQ, toC_smulQ]
  push_cast
  ring

/-! ## Second-order Taylor bounds for polynomials -/

theorem abs_pow_taylor_aux {w c W : ℝ} (hw : 0 ≤ w) (hwW : w ≤ W) (hc : 0 ≤ c) (hcW : c ≤ W) :
    ∀ n : ℕ, |w ^ (n + 2) - c ^ (n + 2) - ((n : ℝ) + 2) * c ^ (n + 1) * (w - c)| ≤
      (((n : ℝ) + 2) * ((n : ℝ) + 1) / 2) * W ^ n * (w - c) ^ 2
  | 0 => by
    have : w ^ (0 + 2) - c ^ (0 + 2) - (((0 : ℕ) : ℝ) + 2) * c ^ (0 + 1) * (w - c) = (w - c) ^ 2 := by
      push_cast; ring
    rw [this, abs_of_nonneg (sq_nonneg _)]
    norm_num
  | n + 1 => by
    have ih := abs_pow_taylor_aux hw hwW hc hcW n
    have hW0 : 0 ≤ W := hw.trans hwW
    calc _ = |w * (w ^ (n + 2) - c ^ (n + 2) - ((n : ℝ) + 2) * c ^ (n + 1) * (w - c)) +
          ((n : ℝ) + 2) * c ^ (n + 1) * (w - c) ^ 2| := by
          congr 1; push_cast; ring
      _ ≤ |w * (w ^ (n + 2) - c ^ (n + 2) - ((n : ℝ) + 2) * c ^ (n + 1) * (w - c))| +
          |((n : ℝ) + 2) * c ^ (n + 1) * (w - c) ^ 2| := abs_add_le _ _
      _ = w * |w ^ (n + 2) - c ^ (n + 2) - ((n : ℝ) + 2) * c ^ (n + 1) * (w - c)| +
          ((n : ℝ) + 2) * c ^ (n + 1) * (w - c) ^ 2 := by
          rw [abs_mul, abs_of_nonneg hw, abs_of_nonneg
            (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hc _)) (sq_nonneg _))]
      _ ≤ W * ((((n : ℝ) + 2) * ((n : ℝ) + 1) / 2) * W ^ n * (w - c) ^ 2) +
          ((n : ℝ) + 2) * W ^ (n + 1) * (w - c) ^ 2 := by
          have hcn : c ^ (n + 1) ≤ W ^ (n + 1) := pow_le_pow_left₀ hc hcW _
          gcongr
      _ = _ := by push_cast; ring

/-- `|wⁿ − cⁿ − n c^{n−1}(w − c)| ≤ n(n−1)/2 · W^{n−2} (w − c)²` for `0 ≤ w, c ≤ W`. -/
theorem abs_pow_taylor_le {w c W : ℝ} (hw : 0 ≤ w) (hwW : w ≤ W) (hc : 0 ≤ c) (hcW : c ≤ W)
    (n : ℕ) : |w ^ n - c ^ n - (n : ℝ) * c ^ (n - 1) * (w - c)| ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * W ^ (n - 2) * (w - c) ^ 2 := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 =>
    have h := abs_pow_taylor_aux hw hwW hc hcW n
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
    push_cast
    refine h.trans (le_of_eq ?_)
    ring

theorem c2Q_eq (f : ℕ → ℚ × ℚ) (W : ℚ) : ∀ L, (c2Q f W L : ℝ) =
    ∑ n ∈ range L, (ab1 (f n) : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) / 2) * (W : ℝ) ^ (n - 2)
  | 0 => by simp [c2Q]
  | L + 1 => by
    rw [c2Q, sum_range_succ, ← c2Q_eq f W L]
    push_cast
    ring

theorem ab1_nonneg (p : ℚ × ℚ) : (0 : ℝ) ≤ (ab1 p : ℝ) := by
  simp only [ab1]; push_cast; positivity

theorem norm_toC_le (p : ℚ × ℚ) : ‖toC p‖ ≤ (ab1 p : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  simp [toC, ab1]

theorem coef_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rcases n with _ | n
  · simp
  · push_cast
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith

theorem c2Q_nonneg (f : ℕ → ℚ × ℚ) {W : ℚ} (hW : (0 : ℝ) ≤ W) (L : ℕ) : (0 : ℝ) ≤ (c2Q f W L : ℝ) := by
  rw [c2Q_eq]
  exact sum_nonneg fun n _ => mul_nonneg (mul_nonneg (ab1_nonneg _) (coef_nonneg n)) (pow_nonneg hW _)

/-- **Second-order Taylor bound for `Φ`**: `‖Φ(w) − Φ(c) − (w − c)Φ'(c)‖ ≤ C₂(W) (w − c)²`. -/
theorem norm_polyC_taylor (f : ℕ → ℚ × ℚ) (L : ℕ) (W : ℚ) {w c : ℝ} (hw : 0 ≤ w) (hwW : w ≤ W)
    (hc : 0 ≤ c) (hcW : c ≤ W) :
    ‖polyC f L w - polyC f L c - ((w - c : ℝ) : ℂ) * DerC f L c‖ ≤ (c2Q f W L : ℝ) * (w - c) ^ 2 := by
  have h : polyC f L w - polyC f L c - ((w - c : ℝ) : ℂ) * DerC f L c =
      ∑ n ∈ range L, toC (f n) * (((w ^ n - c ^ n - (n : ℝ) * c ^ (n - 1) * (w - c)) : ℝ) : ℂ) := by
    simp only [polyC, DerC, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    push_cast
    ring
  rw [h, c2Q_eq, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖toC (f n)‖ * |w ^ n - c ^ n - (n : ℝ) * c ^ (n - 1) * (w - c)|
      ≤ (ab1 (f n) : ℝ) * (((n : ℝ) * ((n : ℝ) - 1) / 2) * (W : ℝ) ^ (n - 2) * (w - c) ^ 2) :=
        mul_le_mul (norm_toC_le _) (abs_pow_taylor_le hw hwW hc hcW n) (abs_nonneg _)
          (ab1_nonneg _)
    _ = _ := by ring

/-! ## The circle -/

/-- `zm(m) = e^{2i arctan m}`. -/
theorem zm_eq_cexp (m : ℝ) : zm m = cexp (((2 * Real.arctan m : ℝ) : ℂ) * I) := by
  have h1 : (0 : ℝ) < 1 + m ^ 2 := by positivity
  have hs : √(1 + m ^ 2) ^ 2 = 1 + m ^ 2 := Real.sq_sqrt h1.le
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow, hs]
    simp only [zm]
    field_simp
    ring
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan,
      show 2 * (m / √(1 + m ^ 2)) * (1 / √(1 + m ^ 2)) = 2 * m / √(1 + m ^ 2) ^ 2 by ring, hs]
    simp only [zm]

theorem abs_arctan_sub_le (x y : ℝ) : |Real.arctan x - Real.arctan y| ≤ |x - y| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := Real.arctan) (C := 1) (fun z _ => Real.differentiable_arctan.differentiableAt)
    (fun z _ => by
      rw [Real.deriv_arctan, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg z]))
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-! ## Expanding `e^{ikδ}` -/

theorem norm_cexp_sub_one_sub_le {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp ((y : ℂ) * I) - 1 - (y : ℂ) * I‖ ≤ y ^ 2 := by
  have hn : ‖(y : ℂ) * I‖ = |y| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have := Complex.norm_exp_sub_one_sub_id_le (x := (y : ℂ) * I) (by rw [hn]; exact hy)
  rwa [hn, sq_abs] at this

theorem norm_cexp_sub_one_le' (y : ℝ) : ‖cexp ((y : ℂ) * I) - 1‖ ≤ |y| := by
  rw [mul_comm]
  simpa [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := y))

/-- One term `Φ zᵏ`, `z = z_c e^{iδ}`, to second order. -/
theorem term_bound {Φ a b zc : ℂ} {δ d ht hw ε : ℝ} (k : ℕ) (hzc : ‖zc‖ = 1)
    (hδ : |δ| ≤ ht) (hd : |d| ≤ hw) (hk : (k : ℝ) * ht ≤ 1) (hρ : ‖Φ - a - (d : ℂ) * b‖ ≤ ε) :
    ‖Φ * (zc * cexp ((δ : ℂ) * I)) ^ k -
        (a * zc ^ k + (δ : ℂ) * I * ((k : ℂ) * (a * zc ^ k)) + (d : ℂ) * (b * zc ^ k))‖ ≤
      ‖a‖ * ((k : ℝ) * ht) ^ 2 + hw * ‖b‖ * ((k : ℝ) * ht) + ε := by
  set y : ℝ := (k : ℝ) * δ with hy_def
  have hy : |y| ≤ (k : ℝ) * ht := by
    rw [hy_def, abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg k)
  have hy1 : |y| ≤ 1 := hy.trans hk
  have hu : (zc * cexp ((δ : ℂ) * I)) ^ k = zc ^ k * cexp ((y : ℂ) * I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 2
    rw [hy_def]; push_cast; ring
  set u := cexp ((y : ℂ) * I) with hu_def
  have hid : Φ * (zc ^ k * u) -
      (a * zc ^ k + (δ : ℂ) * I * ((k : ℂ) * (a * zc ^ k)) + (d : ℂ) * (b * zc ^ k)) =
      zc ^ k * (a * (u - 1 - (y : ℂ) * I) + (d : ℂ) * b * (u - 1) + (Φ - a - (d : ℂ) * b) * u) := by
    rw [hy_def]; push_cast; ring
  rw [hu, hid, norm_mul, norm_pow, hzc, one_pow, one_mul]
  have hu1 : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I y
  have e1 := norm_cexp_sub_one_sub_le hy1
  have e2 := norm_cexp_sub_one_le' y
  have hd' : ‖(d : ℂ)‖ = |d| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hw0 : 0 ≤ hw := (abs_nonneg d).trans hd
  have hn : ‖a * (u - 1 - (y : ℂ) * I) + (d : ℂ) * b * (u - 1) + (Φ - a - (d : ℂ) * b) * u‖ ≤
      ‖a‖ * ‖u - 1 - (y : ℂ) * I‖ + |d| * ‖b‖ * ‖u - 1‖ + ‖Φ - a - (d : ℂ) * b‖ * ‖u‖ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      (le_of_eq (norm_mul _ _)) (le_of_eq ?_))) (le_of_eq (norm_mul _ _)))
    rw [norm_mul, norm_mul, hd']
  rw [hu1, mul_one] at hn
  have h1 : ‖a‖ * ‖u - 1 - (y : ℂ) * I‖ ≤ ‖a‖ * ((k : ℝ) * ht) ^ 2 := by
    refine mul_le_mul_of_nonneg_left (e1.trans ?_) (norm_nonneg _)
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have h2 : |d| * ‖b‖ * ‖u - 1‖ ≤ hw * ‖b‖ * ((k : ℝ) * ht) := by
    have := mul_le_mul hd (le_refl ‖b‖) (norm_nonneg _) hw0
    exact mul_le_mul this (e2.trans hy) (norm_nonneg _) (mul_nonneg hw0 (norm_nonneg _))
  linarith

/-- **`F_K(z, w) = F₀ + iδF_θ + dF_w + O*(E)`**, `z = z_c e^{iδ}`. -/
theorem norm_F_le {Φ1 Φ2 Φ4 a1 a2 a4 b1 b2 b4 zc : ℂ} {δ d ht hw ε1 ε2 ε4 : ℝ}
    (hzc : ‖zc‖ = 1) (hδ : |δ| ≤ ht) (hd : |d| ≤ hw) (hk : 4 * ht ≤ 1)
    (h1 : ‖Φ1 - a1 - (d : ℂ) * b1‖ ≤ ε1) (h2 : ‖Φ2 - a2 - (d : ℂ) * b2‖ ≤ ε2)
    (h4 : ‖Φ4 - a4 - (d : ℂ) * b4‖ ≤ ε4) :
    ‖Φ1 * (zc * cexp ((δ : ℂ) * I)) + Φ2 * (zc * cexp ((δ : ℂ) * I)) ^ 2 +
        Φ4 * (zc * cexp ((δ : ℂ) * I)) ^ 4‖ ≤
      ‖(a1 * zc + a2 * zc ^ 2 + a4 * zc ^ 4) +
          (δ : ℂ) * I * (a1 * zc + 2 * (a2 * zc ^ 2) + 4 * (a4 * zc ^ 4)) +
          (d : ℂ) * (b1 * zc + b2 * zc ^ 2 + b4 * zc ^ 4)‖ +
        ((‖a1‖ * ht ^ 2 + ‖a2‖ * (2 * ht) ^ 2 + ‖a4‖ * (4 * ht) ^ 2) +
          hw * (‖b1‖ * ht + ‖b2‖ * (2 * ht) + ‖b4‖ * (4 * ht)) + (ε1 + ε2 + ε4)) := by
  have ht0 : 0 ≤ ht := (abs_nonneg δ).trans hδ
  have t1 := term_bound 1 hzc hδ hd (by push_cast; linarith) h1
  have t2 := term_bound 2 hzc hδ hd (by push_cast; linarith) h2
  have t4 := term_bound 4 hzc hδ hd (by push_cast; linarith) h4
  simp only [pow_one, Nat.cast_one, one_mul, Nat.cast_ofNat] at t1 t2 t4
  set z := zc * cexp ((δ : ℂ) * I)
  set V := (a1 * zc + a2 * zc ^ 2 + a4 * zc ^ 4) +
    (δ : ℂ) * I * (a1 * zc + 2 * (a2 * zc ^ 2) + 4 * (a4 * zc ^ 4)) +
    (d : ℂ) * (b1 * zc + b2 * zc ^ 2 + b4 * zc ^ 4)
  set T1 := Φ1 * z - (a1 * zc + (δ : ℂ) * I * (a1 * zc) + (d : ℂ) * (b1 * zc))
  set T2 := Φ2 * z ^ 2 - (a2 * zc ^ 2 + (δ : ℂ) * I * (2 * (a2 * zc ^ 2)) + (d : ℂ) * (b2 * zc ^ 2))
  set T4 := Φ4 * z ^ 4 - (a4 * zc ^ 4 + (δ : ℂ) * I * (4 * (a4 * zc ^ 4)) + (d : ℂ) * (b4 * zc ^ 4))
  have hsplit : Φ1 * z + Φ2 * z ^ 2 + Φ4 * z ^ 4 = V + (T1 + T2 + T4) := by
    simp only [V, T1, T2, T4]; ring
  rw [hsplit]
  have := norm_add_le V (T1 + T2 + T4)
  have := norm_add_le (T1 + T2) T4
  have := norm_add_le T1 T2
  linarith

/-- `|A + δB + dC|² ≤ |A|² + 2hθ|⟨A, B⟩| + 2h_w|⟨A, C⟩| + 2hθ²|B|² + 2h_w²|C|²`. -/
theorem quad_le {A1 A2 B1 B2 C1 C2 δ d ht hw : ℝ} (hδ : |δ| ≤ ht) (hd : |d| ≤ hw) :
    (A1 + δ * B1 + d * C1) ^ 2 + (A2 + δ * B2 + d * C2) ^ 2 ≤
      (A1 ^ 2 + A2 ^ 2) + 2 * ht * |A1 * B1 + A2 * B2| + 2 * hw * |A1 * C1 + A2 * C2| +
        2 * ht ^ 2 * (B1 ^ 2 + B2 ^ 2) + 2 * hw ^ 2 * (C1 ^ 2 + C2 ^ 2) := by
  have lin : ∀ {x X h : ℝ}, |x| ≤ h → 2 * x * X ≤ 2 * h * |X| := by
    intro x X h hx
    calc 2 * x * X ≤ 2 * |x * X| := by linarith [le_abs_self (x * X)]
      _ = 2 * |x| * |X| := by rw [abs_mul]; ring
      _ ≤ 2 * h * |X| := by gcongr
  have h1 := lin (X := A1 * B1 + A2 * B2) hδ
  have h2 := lin (X := A1 * C1 + A2 * C2) hd
  have h3 : (δ * B1 + d * C1) ^ 2 ≤ 2 * δ ^ 2 * B1 ^ 2 + 2 * d ^ 2 * C1 ^ 2 := by
    nlinarith [sq_nonneg (δ * B1 - d * C1)]
  have h4 : (δ * B2 + d * C2) ^ 2 ≤ 2 * δ ^ 2 * B2 ^ 2 + 2 * d ^ 2 * C2 ^ 2 := by
    nlinarith [sq_nonneg (δ * B2 - d * C2)]
  have hδ2 : δ ^ 2 ≤ ht ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  have hd2 : d ^ 2 ≤ hw ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hB := mul_le_mul_of_nonneg_right hδ2 (add_nonneg (sq_nonneg B1) (sq_nonneg B2))
  have hC := mul_le_mul_of_nonneg_right hd2 (add_nonneg (sq_nonneg C1) (sq_nonneg C2))
  have e : (A1 + δ * B1 + d * C1) ^ 2 + (A2 + δ * B2 + d * C2) ^ 2 =
      (A1 ^ 2 + A2 ^ 2) + 2 * δ * (A1 * B1 + A2 * B2) + 2 * d * (A1 * C1 + A2 * C2) +
        ((δ * B1 + d * C1) ^ 2 + (δ * B2 + d * C2) ^ 2) := by ring
  rw [e]
  linarith

/-! ## Soundness of a cell of region B -/

theorem toC_zQ (s m : ℚ) : toC (zQ s m) = ((s : ℝ) : ℂ) * zm m := by
  apply Complex.ext <;> simp [toC, zQ, zm] <;> ring

theorem toC_sq3 (z a1 a2 a4 : ℚ × ℚ) (c1 c2 c4 : ℚ) :
    toC (sq3 z a1 a2 a4 c1 c2 c4) = (c1 : ℂ) * (toC a1 * toC z) + (c2 : ℂ) * (toC a2 * toC z ^ 2) +
      (c4 : ℂ) * (toC a4 * toC z ^ 4) := by
  simp only [sq3, toC_cadd, toC_smulQ, toC_cmul]; ring

theorem RK_eq (W : ℚ) : RK KB W = RKQ W := by
  unfold RK RKQ; push_cast; ring

theorem RK_mono {w W : ℝ} (hw : 0 ≤ w) (h : w ≤ W) : RK KB w ≤ RK KB W := by
  unfold RK
  have : (0 : ℝ) ≤ 4 * (KB.factorial : ℝ) * (4 ^ (KB + 1) - 1) := by
    norm_num [KB, Nat.factorial]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw h _) this

theorem cellB'_sound {ht hw W : ℚ} {z1 a1 a2 a4 b1 b2 b4 : ℚ × ℚ}
    (h : cellB' ht hw W z1 a1 a2 a4 b1 b2 b4 = true) {zc : ℂ} (hz : toC z1 = zc) (hzc : ‖zc‖ = 1)
    {δ d w : ℝ} (hδ : |δ| ≤ ht) (hd : |d| ≤ hw) (hw0 : 0 ≤ w) (hwW : w ≤ W) {Φ1 Φ2 Φ4 : ℂ}
    (h1 : ‖Φ1 - toC a1 - (d : ℂ) * toC b1‖ ≤ (c2Q f1 W (KB + 1) : ℝ) * (hw : ℝ) ^ 2)
    (h2 : ‖Φ2 - toC a2 - (d : ℂ) * toC b2‖ ≤ (c2Q f2 W (KB + 1) : ℝ) * (hw : ℝ) ^ 2)
    (h4 : ‖Φ4 - toC a4 - (d : ℂ) * toC b4‖ ≤ (c2Q f4 W (KB + 1) : ℝ) * (hw : ℝ) ^ 2) :
    ‖Φ1 * (zc * cexp ((δ : ℂ) * I)) + Φ2 * (zc * cexp ((δ : ℂ) * I)) ^ 2 +
        Φ4 * (zc * cexp ((δ : ℂ) * I)) ^ 4‖ + RK KB w ≤ BB := by
  simp only [cellB', Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hM⟩, hQ⟩ := h
  set E := eB ht hw W a1 a2 a4 b1 b2 b4 with hE
  set M := BB - RKQ W - E with hMdef
  have hkR : 4 * (ht : ℝ) ≤ 1 := by exact_mod_cast hk
  have hF := norm_F_le hzc hδ hd hkR h1 h2 h4
  set F0 := sq3 z1 a1 a2 a4 1 1 1
  set Ft := sq3 z1 a1 a2 a4 1 2 4
  set Fw := sq3 z1 b1 b2 b4 1 1 1
  set V := (toC a1 * zc + toC a2 * zc ^ 2 + toC a4 * zc ^ 4) +
    (δ : ℂ) * I * (toC a1 * zc + 2 * (toC a2 * zc ^ 2) + 4 * (toC a4 * zc ^ 4)) +
    (d : ℂ) * (toC b1 * zc + toC b2 * zc ^ 2 + toC b4 * zc ^ 4)
  have hV : V = toC F0 + (δ : ℂ) * I * toC Ft + (d : ℂ) * toC Fw := by
    simp only [V, F0, Ft, Fw, toC_sq3, hz]; push_cast; ring
  -- `‖V‖ ≤ M`
  have hVre : V.re = (F0.1 : ℝ) + δ * (-(Ft.2 : ℝ)) + d * (Fw.1 : ℝ) := by
    rw [hV]; simp [toC]
  have hVim : V.im = (F0.2 : ℝ) + δ * (Ft.1 : ℝ) + d * (Fw.2 : ℝ) := by
    rw [hV]; simp [toC]
  have hq := quad_le (A1 := (F0.1 : ℝ)) (A2 := F0.2) (B1 := -(Ft.2 : ℝ)) (B2 := Ft.1)
    (C1 := Fw.1) (C2 := Fw.2) hδ hd
  have hqB : ((qB ht hw F0 Ft Fw : ℚ) : ℝ) = ((F0.1 : ℝ) ^ 2 + (F0.2 : ℝ) ^ 2) +
      2 * (ht : ℝ) * |(F0.1 : ℝ) * -(Ft.2 : ℝ) + (F0.2 : ℝ) * (Ft.1 : ℝ)| +
      2 * (hw : ℝ) * |(F0.1 : ℝ) * (Fw.1 : ℝ) + (F0.2 : ℝ) * (Fw.2 : ℝ)| +
      2 * (ht : ℝ) ^ 2 * ((-(Ft.2 : ℝ)) ^ 2 + (Ft.1 : ℝ) ^ 2) +
      2 * (hw : ℝ) ^ 2 * ((Fw.1 : ℝ) ^ 2 + (Fw.2 : ℝ) ^ 2) := by
    simp only [qB, nsqQ, dotQ]; push_cast; ring_nf
  have hQR : ((qB ht hw F0 Ft Fw : ℚ) : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hQ
  have hMR : (0 : ℝ) ≤ M := by exact_mod_cast hM
  have hVn : ‖V‖ ≤ M := by
    have hsq : ‖V‖ ^ 2 = V.re ^ 2 + V.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have : ‖V‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
      rw [hsq, hVre, hVim]; linarith
    exact (sq_le_sq₀ (norm_nonneg _) hMR).1 this
  -- the error terms
  have hER : (‖toC a1‖ * (ht : ℝ) ^ 2 + ‖toC a2‖ * (2 * (ht : ℝ)) ^ 2 + ‖toC a4‖ * (4 * (ht : ℝ)) ^ 2) +
      (hw : ℝ) * (‖toC b1‖ * ht + ‖toC b2‖ * (2 * ht) + ‖toC b4‖ * (4 * ht)) +
      ((c2Q f1 W (KB + 1) : ℝ) * (hw : ℝ) ^ 2 + (c2Q f2 W (KB + 1) : ℝ) * (hw : ℝ) ^ 2 +
        (c2Q f4 W (KB + 1) : ℝ) * (hw : ℝ) ^ 2) ≤ (E : ℝ) := by
    have ht0 : (0 : ℝ) ≤ ht := (abs_nonneg δ).trans hδ
    have hw0' : (0 : ℝ) ≤ hw := (abs_nonneg d).trans hd
    have ea1 := norm_toC_le a1
    have ea2 := norm_toC_le a2
    have ea4 := norm_toC_le a4
    have eb1 := norm_toC_le b1
    have eb2 := norm_toC_le b2
    have eb4 := norm_toC_le b4
    rw [hE]
    simp only [eB]
    push_cast
    have k1 : ‖toC a1‖ * (ht : ℝ) ^ 2 ≤ (ab1 a1 : ℝ) * (ht : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right ea1 (sq_nonneg _)
    have k2 : ‖toC a2‖ * (2 * (ht : ℝ)) ^ 2 ≤ (ab1 a2 : ℝ) * (2 * (ht : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right ea2 (sq_nonneg _)
    have k4 : ‖toC a4‖ * (4 * (ht : ℝ)) ^ 2 ≤ (ab1 a4 : ℝ) * (4 * (ht : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right ea4 (sq_nonneg _)
    have l1 : ‖toC b1‖ * (ht : ℝ) ≤ (ab1 b1 : ℝ) * ht := mul_le_mul_of_nonneg_right eb1 ht0
    have l2 : ‖toC b2‖ * (2 * (ht : ℝ)) ≤ (ab1 b2 : ℝ) * (2 * ht) :=
      mul_le_mul_of_nonneg_right eb2 (by positivity)
    have l4 : ‖toC b4‖ * (4 * (ht : ℝ)) ≤ (ab1 b4 : ℝ) * (4 * ht) :=
      mul_le_mul_of_nonneg_right eb4 (by positivity)
    have l := mul_le_mul_of_nonneg_left (add_le_add (add_le_add l1 l2) l4) hw0'
    linarith
  have hRK : RK KB w ≤ RKQ W := (RK_mono hw0 hwW).trans (le_of_eq (RK_eq W))
  have hMv : (M : ℝ) = BB - RKQ W - E := by rw [hMdef]; push_cast; ring
  linarith

/-- The conclusion of a check of region B. -/
def GoodB (s m0 m1 w0 w1 : ℚ) : Prop :=
  ∀ m w : ℝ, (m0 : ℝ) ≤ m → m ≤ m1 → (w0 : ℝ) ≤ w → w ≤ w1 →
    ‖FK KB (((s : ℝ) : ℂ) * zm m) w‖ + RK KB w ≤ BB

theorem cellB_sound {s m0 m1 w0 w1 : ℚ} (hs : s = 1 ∨ s = -1) (hw0 : 0 ≤ w0)
    (h : cellB s m0 m1 w0 w1 = true) : GoodB s m0 m1 w0 w1 := by
  intro m w hm0 hm1 hw0' hw1
  simp only [cellB] at h
  set mc : ℚ := (m0 + m1) / 2 with hmc
  set wc : ℚ := (w0 + w1) / 2 with hwc
  have hw0R : (0 : ℝ) ≤ w0 := by exact_mod_cast hw0
  have hw : 0 ≤ w := hw0R.trans hw0'
  have hwc0 : (0 : ℝ) ≤ wc := by rw [hwc]; push_cast; linarith
  have hwc1 : (wc : ℝ) ≤ w1 := by rw [hwc]; push_cast; linarith
  -- the circle
  set δ : ℝ := 2 * Real.arctan m - 2 * Real.arctan mc with hδdef
  have hzm : zm m = zm mc * cexp ((δ : ℂ) * I) := by
    rw [zm_eq_cexp, zm_eq_cexp, ← Complex.exp_add]; congr 1; rw [hδdef]; push_cast; ring
  have hδ : |δ| ≤ ((m1 - m0 : ℚ) : ℝ) := by
    have h1 := abs_arctan_sub_le m mc
    have h2 : |m - (mc : ℝ)| ≤ ((m1 : ℝ) - m0) / 2 := by
      rw [hmc]; push_cast; rw [abs_le]; constructor <;> linarith
    calc |δ| = 2 * |Real.arctan m - Real.arctan mc| := by
          rw [hδdef, ← mul_sub, abs_mul, abs_two]
      _ ≤ 2 * |m - mc| := by gcongr
      _ ≤ _ := by push_cast; linarith
  -- the point `w`
  set d : ℝ := w - wc with hddef
  have hd : |d| ≤ (((w1 - w0) / 2 : ℚ) : ℝ) := by
    rw [hddef, hwc]; push_cast; rw [abs_le]; constructor <;> linarith
  have hT : ∀ f : ℕ → ℚ × ℚ, ‖polyC f (KB + 1) w - toC (hornQ f wc (KB + 1) 0) -
      (d : ℂ) * toC (hornQ (dQ f) wc KB 0)‖ ≤
      (c2Q f w1 (KB + 1) : ℝ) * ((((w1 - w0) / 2 : ℚ) : ℝ)) ^ 2 := by
    intro f
    rw [toC_hornQ_zero, toC_hornQ_dQ]
    refine (norm_polyC_taylor f (KB + 1) w1 hw hw1 hwc0 hwc1).trans ?_
    have hd2 : (w - wc) ^ 2 ≤ ((((w1 - w0) / 2 : ℚ) : ℝ)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    exact mul_le_mul_of_nonneg_left hd2 (c2Q_nonneg f (by linarith) _)
  have hzc := norm_s_zm hs (mc : ℝ)
  have key := cellB'_sound h (toC_zQ s mc) hzc hδ hd hw hw1 (hT f1) (hT f2) (hT f4)
  rw [hzm, ← mul_assoc]
  exact key

theorem chkB_sound {s : ℚ} (hs : s = 1 ∨ s = -1) :
    ∀ (n : ℕ) (m0 m1 w0 w1 : ℚ), 0 ≤ w0 → chkB n s m0 m1 w0 w1 = true → GoodB s m0 m1 w0 w1
  | 0, m0, m1, w0, w1, hw0, h => cellB_sound hs hw0 h
  | n + 1, m0, m1, w0, w1, hw0, h => by
    simp only [chkB, Bool.or_eq_true] at h
    rcases h with h | h
    · exact cellB_sound hs hw0 h
    · intro m w hm0 hm1 hw0' hw1
      split_ifs at h with hsplit
      · simp only [Bool.and_eq_true] at h
        rcases le_total m (((m0 + m1) / 2 : ℚ) : ℝ) with hm | hm
        · exact chkB_sound hs n _ _ _ _ hw0 h.1 m w hm0 hm hw0' hw1
        · exact chkB_sound hs n _ _ _ _ hw0 h.2 m w hm hm1 hw0' hw1
      · simp only [Bool.and_eq_true] at h
        rcases le_total w (((w0 + w1) / 2 : ℚ) : ℝ) with hw | hw
        · exact chkB_sound hs n _ _ _ _ hw0 h.1 m w hm0 hm1 hw0' hw
        · have : (0 : ℚ) ≤ (w0 + w1) / 2 := by
            have : (w0 : ℝ) ≤ w1 := hw0'.trans hw1
            have : w0 ≤ w1 := by exact_mod_cast this
            linarith
          exact chkB_sound hs n _ _ _ _ this h.2 m w hm0 hm1 hw hw1

theorem GoodB_union {s a b c w0 w1 : ℚ} (h1 : GoodB s a b w0 w1) (h2 : GoodB s b c w0 w1) :
    GoodB s a c w0 w1 := by
  intro m w ha hc hw0 hw1
  rcases le_total m b with h | h
  · exact h1 m w ha h hw0 hw1
  · exact h2 m w h hc hw0 hw1

/-- Chunks `0, …, N` of width `δ` give `[a, a + (N + 1)δ] × [0, W]`. -/
theorem GoodB_of_chunks {s : ℚ} (hs : s = 1 ∨ s = -1) (a δ W : ℚ) :
    ∀ N : ℕ, (∀ i ≤ N, chunkB s a δ W i = true) → GoodB s a (a + ((N : ℚ) + 1) * δ) 0 W
  | 0, h => by
    simp only [chunkB] at h
    have := chkB_sound hs 40 _ _ _ _ le_rfl (h 0 le_rfl)
    simpa using this
  | N + 1, h => by
    have h1 := GoodB_of_chunks hs a δ W N fun i hi => h i (by omega)
    simp only [chunkB] at h
    have h2 := chkB_sound hs 40 _ _ _ _ le_rfl (h (N + 1) le_rfl)
    rw [show a + ((N : ℚ) + 1) * δ = a + ((N + 1 : ℕ) : ℚ) * δ by push_cast; ring] at h1
    exact GoodB_union h1 h2

/-! ## Region A -/

/-- The conclusion of a check of region A. -/
def GoodA (x0 x1 : ℚ) : Prop :=
  ∀ x : ℝ, (x0 : ℝ) ≤ x → x ≤ x1 → ‖eta2DD (x / (2 * π))‖ ≤ BB

theorem cellA_sound {x0 x1 : ℚ} (h0 : 0 ≤ x0) (h1 : x1 ≤ XA) (h : cellA x0 x1 = true) :
    GoodA x0 x1 := by
  intro x hx0 hx1
  simp only [cellA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hM, hF⟩ := h
  set xc : ℚ := (x0 + x1) / 2 with hxc
  set F := PQ NA xc
  set M : ℚ := BB - 12 * (x1 - x0) - errA with hMdef
  have hxc0 : (0 : ℝ) ≤ xc := by
    have : (0 : ℝ) ≤ x0 := by exact_mod_cast h0
    rw [hxc]; push_cast; linarith
  have hxcX : (xc : ℝ) ≤ XA := by
    have : (x1 : ℝ) ≤ XA := by exact_mod_cast h1
    rw [hxc]; push_cast; linarith
  have hcond : |(xc : ℝ)| / (NA + 1) ≤ 1 / 2 := by
    rw [abs_of_nonneg hxc0, div_le_iff₀ (by positivity)]
    simp only [NA, XA] at hxcX ⊢; push_cast at hxcX ⊢; linarith
  have hT := norm_eta2DD_sub_P hcond
  have hPc : ‖PN NA xc‖ ≤ M := by
    rw [← toC_PQ]
    have h1 := norm_sq_toC F
    have hM' : (0 : ℝ) ≤ M := by exact_mod_cast hM
    have hF' : ((F.1 ^ 2 + F.2 ^ 2 : ℚ) : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hF
    exact (sq_le_sq₀ (norm_nonneg _) hM').1 (h1 ▸ hF')
  have herr : 120 * (|(xc : ℝ)| ^ NA / NA.factorial) ≤ errA := by
    rw [abs_of_nonneg hxc0]
    have : (xc : ℝ) ^ NA ≤ (XA : ℝ) ^ NA := pow_le_pow_left₀ hxc0 hxcX NA
    simp only [errA]; push_cast
    have hf : (0 : ℝ) < NA.factorial := by exact_mod_cast Nat.factorial_pos _
    rw [mul_div_assoc]
    gcongr
  have hL := norm_eta2DD_sub_le x xc
  have hd : |x - (xc : ℝ)| ≤ ((x1 : ℝ) - x0) / 2 := by
    rw [hxc]; push_cast; rw [abs_le]; constructor <;> linarith
  have hMv : (M : ℝ) = BB - 12 * ((x1 : ℝ) - x0) - errA := by rw [hMdef]; push_cast; ring
  have := norm_sub_norm_le (eta2DD (x / (2 * π))) (eta2DD ((xc : ℝ) / (2 * π)))
  have := norm_sub_norm_le (eta2DD ((xc : ℝ) / (2 * π))) (PN NA xc)
  linarith

theorem chkA_sound : ∀ (n : ℕ) (x0 x1 : ℚ), 0 ≤ x0 → x1 ≤ XA → chkA n x0 x1 = true → GoodA x0 x1
  | 0, x0, x1, h0, h1, h => cellA_sound h0 h1 h
  | n + 1, x0, x1, h0, h1, h => by
    simp only [chkA, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨ha, hb⟩
    · exact cellA_sound h0 h1 h
    · intro x hx0 hx1
      have hx01 : x0 ≤ x1 := by exact_mod_cast hx0.trans hx1
      rcases le_total x (((x0 + x1) / 2 : ℚ) : ℝ) with hx | hx
      · exact chkA_sound n _ _ h0 (by linarith) ha x hx0 hx
      · exact chkA_sound n _ _ (by linarith) h1 hb x hx hx1

theorem GoodA_union {a b c : ℚ} (h1 : GoodA a b) (h2 : GoodA b c) : GoodA a c := by
  intro x ha hc
  rcases le_total x b with h | h
  · exact h1 x ha h
  · exact h2 x h hc

/-- Chunks `0, …, N` of width `δ` give `[a, a + (N + 1)δ]`. -/
theorem GoodA_of_chunks {a δ : ℚ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    ∀ N : ℕ, a + ((N : ℚ) + 1) * δ ≤ XA → (∀ i ≤ N, chunkA a δ i = true) →
      GoodA a (a + ((N : ℚ) + 1) * δ)
  | 0, hX, h => by
    simp only [chunkA] at h
    have := chkA_sound 20 _ _ (by simpa using ha) (by simpa using hX) (h 0 le_rfl)
    simpa using this
  | N + 1, hX, h => by
    have hX' : a + ((N : ℚ) + 1) * δ ≤ XA := by
      refine le_trans ?_ hX; push_cast; nlinarith
    have h1 := GoodA_of_chunks ha hδ N hX' fun i hi => h i (by omega)
    simp only [chunkA] at h
    have h2 := chkA_sound 20 _ _ (by positivity) hX (h (N + 1) le_rfl)
    rw [show a + ((N : ℚ) + 1) * δ = a + ((N + 1 : ℕ) : ℚ) * δ by push_cast; ring] at h1
    exact GoodA_union h1 h2

end RSBounds.HelfgottB6
