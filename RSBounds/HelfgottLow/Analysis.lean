import RSBounds.HelfgottSmall.Walk
import RSBounds.HelfgottLow.DataChecks

/-!
# What the walk's numbers mean

* every anchor `(a, l, lo, r)` has `2 ≤ a`, `lo / SC ≤ log a ≤ l / SC` and `SC / √a ≤ r`;
* `lowW n a lo` bounds `SC · log n` from below when `a ≤ n`;
* `incR n a r inc` bounds `SC · Λ(n) / √n` from above when `Λ(n) ≤ inc / SC`.
-/

namespace RSBounds.HelfgottLow

open Real Finset ArithmeticFunction
open RSBounds.HelfgottSmall (SC SC_pos expPoly expPoly_eq log_le_of_expCheck nat_le_mul_ceilDiv
  force_eq)

/-! ### Anchors -/

theorem log_ge_of_expCheckLo {a b V : ℕ} (ha : 0 < a) (h : expCheckLo a b V = true) :
    Real.log a + V / SC ≤ Real.log b := by
  simp only [expCheckLo, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨hV, h⟩ := h
  have hSC := SC_pos
  set x : ℝ := (V : ℝ) / SC with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hSC]
    exact_mod_cast hV
  have he := Real.exp_bound' hx0 hx1 (n := 9) (by norm_num)
  set T := ∑ i ∈ range 9, x ^ i / (Nat.factorial i : ℝ) with hT
  have h1 : (a : ℝ) * (81 * (SC : ℝ) * (expPoly V : ℝ) + 10 * (V : ℝ) ^ 9) ≤
      b * (81 * 40320 * (SC : ℝ) ^ 9) := by exact_mod_cast h
  rw [expPoly_eq] at h1
  change (a : ℝ) * (81 * (SC : ℝ) * (40320 * (SC : ℝ) ^ 8 * T) + 10 * (V : ℝ) ^ 9) ≤ _ at h1
  have hV9 : (V : ℝ) = x * SC := by rw [hx]; field_simp
  rw [hV9] at h1
  have hexp : Real.exp x ≤ T + x ^ 9 * 10 / 3265920 := by
    have hT' : T = ∑ i ∈ range 9, x ^ i / (Nat.factorial i : ℝ) := rfl
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at he hT'
    norm_num at he hT'
    rw [hT']
    linarith
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have key : (a : ℝ) * (T + x ^ 9 * 10 / 3265920) ≤ b := by
    have hS : (0 : ℝ) < 3265920 * (SC : ℝ) ^ 9 := by positivity
    have : (a : ℝ) * (T + x ^ 9 * 10 / 3265920) * (3265920 * (SC : ℝ) ^ 9) ≤
        b * (3265920 * (SC : ℝ) ^ 9) := by
      calc (a : ℝ) * (T + x ^ 9 * 10 / 3265920) * (3265920 * (SC : ℝ) ^ 9)
          = (a : ℝ) * (81 * (SC : ℝ) * (40320 * (SC : ℝ) ^ 8 * T) + 10 * (x * SC) ^ 9) := by ring
        _ ≤ b * (81 * 40320 * (SC : ℝ) ^ 9) := h1
        _ = b * (3265920 * (SC : ℝ) ^ 9) := by ring
    exact le_of_mul_le_mul_right this hS
  have hb : (a : ℝ) * Real.exp x ≤ b := le_trans (by gcongr) key
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le (by positivity) hb
  calc Real.log a + x = Real.log (a * Real.exp x) := by
        rw [Real.log_mul ha'.ne' (Real.exp_pos x).ne', Real.log_exp]
    _ ≤ Real.log b := Real.log_le_log (by positivity) hb

/-- The logarithm bounds of an anchor. -/
def LogGood (x : Anc) : Prop :=
  2 ≤ x.1 ∧ Real.log x.1 ≤ x.2.1 / SC ∧ (x.2.2.1 : ℝ) / SC ≤ Real.log x.1

/-- Everything an anchor has. -/
def Good (x : Anc) : Prop := LogGood x ∧ SC * SC ≤ x.2.2.2 * x.2.2.2 * x.1

theorem chainOK_good : ∀ (L : List Anc) (x : Anc), chainOK (x :: L) = true →
    LogGood x → ∀ y ∈ x :: L, LogGood y := by
  intro L
  induction L with
  | nil =>
    intro x _ hx y hy
    simp only [List.mem_singleton] at hy
    exact hy ▸ hx
  | cons z L ih =>
    intro x h hx y hy
    obtain ⟨a, l, lo, r⟩ := x
    obtain ⟨b, l', lo', r'⟩ := z
    simp only [chainOK, pairOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨⟨hab, hll⟩, hexp⟩, hlo⟩, hexpLo⟩, hrest⟩ := h
    have hz : LogGood (b, l', lo', r') := by
      obtain ⟨ha2, hal, hlol⟩ := hx
      simp only at ha2 hal hlol
      refine ⟨by simp only; omega, ?_, ?_⟩
      · simp only
        have h1 := log_le_of_expCheck (by omega) hexp
        have h2 : ((l' - l : ℕ) : ℝ) = (l' : ℝ) - l := by push_cast [hll]; ring
        rw [h2] at h1
        calc Real.log b ≤ Real.log a + ((l' : ℝ) - l) / SC := h1
          _ ≤ l / SC + ((l' : ℝ) - l) / SC := by linarith
          _ = l' / SC := by ring
      · simp only
        have h1 := log_ge_of_expCheckLo (by omega) hexpLo
        have h2 : ((lo' - lo : ℕ) : ℝ) = (lo' : ℝ) - lo := by push_cast [hlo]; ring
        rw [h2] at h1
        calc (lo' : ℝ) / SC = lo / SC + ((lo' : ℝ) - lo) / SC := by ring
          _ ≤ Real.log a + ((lo' : ℝ) - lo) / SC := by linarith
          _ ≤ Real.log b := h1
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact ih (b, l', lo', r') hrest hz y hy

theorem log_two_bounds :
    Real.log 2 ≤ (693147180800000 : ℕ) / SC ∧ ((693147180300000 : ℕ) : ℝ) / SC ≤ Real.log 2 := by
  have h1 := Real.log_two_lt_d9
  have h2 := Real.log_two_gt_d9
  constructor
  · norm_num [SC] at h1 ⊢; linarith
  · norm_num [SC] at h2 ⊢; linarith

theorem anchor_good {x : Anc} (hx : x ∈ anchorsAll) : Good x := by
  obtain ⟨t, ht⟩ : ∃ t, anchorsAll = (2, 693147180800000, 693147180300000, 707106781186548) :: t := by
    have h := anchors_head
    cases hL : anchorsAll with
    | nil => rw [hL] at h; simp at h
    | cons y t => rw [hL] at h; simp only [List.head?_cons, Option.some.injEq] at h; exact ⟨t, h ▸ rfl⟩
  refine ⟨?_, ?_⟩
  · have hx' := hx
    rw [ht] at hx'
    have hc := anchors_chainOK
    rw [ht] at hc
    exact chainOK_good t _ hc ⟨le_rfl, by exact_mod_cast log_two_bounds.1,
      by exact_mod_cast log_two_bounds.2⟩ x hx'
  · have h := anchors_rOK
    simp only [rOK, List.all_eq_true, Nat.ble_eq] at h
    exact h x hx

theorem getD_mem {i : ℕ} (h : (anchorsAll.getD i dflt).1 ≠ 0) : anchorsAll.getD i dflt ∈ anchorsAll := by
  by_cases hi : i < anchorsAll.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (by omega)] at h
    simp [dflt] at h

/-! ### Lower bounds for `log`, upper bounds for `1 / √n` -/

theorem lowW_le {n a lo : ℕ} (ha : 0 < a) (han : a ≤ n) (hlo : (lo : ℝ) / SC ≤ Real.log a) :
    (lowW n a lo : ℝ) / SC ≤ Real.log n := by
  have hSC := SC_pos
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set c := (n - a) * SC / n with hc
  have hcN : n * c ≤ (n - a) * SC := Nat.mul_div_le _ _
  have hw : (lowW n a lo : ℝ) = lo + c := by
    have : lowW n a lo = lo + c := rfl
    rw [this]; push_cast; ring
  have h1 : ((n : ℝ) - a) / n ≤ Real.log n - Real.log a := by
    have := Real.log_le_sub_one_of_pos (div_pos ha' hn')
    rw [Real.log_div ha'.ne' hn'.ne'] at this
    have e : (a : ℝ) / n - 1 = -(((n : ℝ) - a) / n) := by field_simp; ring
    linarith
  have h2 : (c : ℝ) / SC ≤ ((n : ℝ) - a) / n := by
    rw [div_le_div_iff₀ hSC hn']
    have : ((n * c : ℕ) : ℝ) ≤ (((n - a) * SC : ℕ) : ℝ) := by exact_mod_cast hcN
    push_cast [han] at this
    linarith
  rw [hw]
  calc ((lo : ℝ) + c) / SC = lo / SC + c / SC := by ring
    _ ≤ Real.log a + (Real.log n - Real.log a) := by linarith
    _ = Real.log n := by ring

theorem inv_sqrt_le {n a r : ℕ} (ha : 0 < a) (hn : 0 < n) (hr : SC * SC ≤ r * r * a) :
    1 / √(n : ℝ) ≤ (r : ℝ) * (a + n) / (2 * n * SC) := by
  have hSC := SC_pos
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set u := √(a : ℝ) with hu
  set v := √(n : ℝ) with hv
  have hu0 : 0 < u := Real.sqrt_pos.mpr ha'
  have hv0 : 0 < v := Real.sqrt_pos.mpr hn'
  have hu2 : u ^ 2 = a := Real.sq_sqrt ha'.le
  have hv2 : v ^ 2 = n := Real.sq_sqrt hn'.le
  have hr' : (SC : ℝ) * SC ≤ r * r * a := by exact_mod_cast hr
  have hSCru : (SC : ℝ) ≤ r * u := by
    have h0 : (0 : ℝ) ≤ r * u := by positivity
    have : (SC : ℝ) ^ 2 ≤ (r * u) ^ 2 := by rw [mul_pow, hu2]; nlinarith
    exact (pow_le_pow_iff_left₀ hSC.le h0 (by norm_num)).mp this
  rw [← hu2, ← hv2]
  rw [div_le_div_iff₀ hv0 (by positivity)]
  have hamgm : 2 * u * v ≤ u ^ 2 + v ^ 2 := by nlinarith [sq_nonneg (u - v)]
  have : 2 * v ^ 2 * SC ≤ 2 * v ^ 2 * (r * u) := by gcongr
  nlinarith [mul_le_mul_of_nonneg_left hamgm (show (0 : ℝ) ≤ r * v by positivity)]

theorem incR_ge {n a r inc : ℕ} (hn : 0 < n) :
    (inc : ℝ) * r * (a + n) ≤ (incR n a r inc : ℝ) * (2 * n * SC) := by
  have hd : 0 < 2 * n * SC := Nat.mul_pos (Nat.mul_pos (by norm_num) hn) (by norm_num [SC])
  have h := nat_le_mul_ceilDiv (inc * r * (a + n)) (2 * n * SC) hd
  have e : incR n a r inc = (inc * r * (a + n) + (2 * n * SC - 1)) / (2 * n * SC) := by
    unfold incR; rw [force_eq]; rfl
  rw [e]
  have : ((inc * r * (a + n) : ℕ) : ℝ) ≤
      ((2 * n * SC * ((inc * r * (a + n) + (2 * n * SC - 1)) / (2 * n * SC)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at this
  linarith

/-- The `t`-increment: for `0 ≤ x ≤ 1 / √n`, `Λ(n) (1/√n - x) ≤ incR / SC - x · inc / SC`. -/
theorem incR_spec {n a r inc : ℕ} {L x : ℝ} (ha : 0 < a) (hn : 0 < n)
    (hr : SC * SC ≤ r * r * a) (hL : L ≤ inc / SC)
    (hx : x ≤ 1 / √(n : ℝ)) :
    L * (1 / √(n : ℝ) - x) ≤ (incR n a r inc : ℝ) / SC - x * (inc / SC) := by
  have hSC := SC_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := inv_sqrt_le ha hn hr
  have h2 := incR_ge (a := a) (r := r) (inc := inc) hn
  have hinc0 : (0 : ℝ) ≤ inc := Nat.cast_nonneg _
  have h3 : (inc : ℝ) / SC * (1 / √(n : ℝ)) ≤ (incR n a r inc : ℝ) / SC := by
    calc (inc : ℝ) / SC * (1 / √(n : ℝ)) ≤ (inc : ℝ) / SC * ((r : ℝ) * (a + n) / (2 * n * SC)) := by
          gcongr
      _ = ((inc : ℝ) * r * (a + n)) / (2 * n * SC) / SC := by ring
      _ ≤ ((incR n a r inc : ℝ) * (2 * n * SC)) / (2 * n * SC) / SC := by gcongr
      _ = (incR n a r inc : ℝ) / SC := by field_simp
  have h4 : L * (1 / √(n : ℝ) - x) ≤ (inc : ℝ) / SC * (1 / √(n : ℝ) - x) :=
    mul_le_mul_of_nonneg_right hL (by linarith)
  nlinarith

end RSBounds.HelfgottLow
