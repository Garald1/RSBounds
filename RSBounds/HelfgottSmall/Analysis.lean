import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import RSBounds.HelfgottSmall.DataChecks

/-!
# What the walk's numbers mean

* every anchor `(a, l)` has `2 ≤ a` and `log a ≤ l / SC`;
* the weight `weight n a l` bounds `SC · log n` from above when `a ≤ n`;
* every prime passes `isSurv`, every prime below 5001 is in `smallD`;
* the events are strictly sorted and contain every prime power `p ^ k ≤ NMAX` with `k ≥ 2`.
-/

namespace RSBounds.HelfgottSmall

open Real Finset ArithmeticFunction

theorem SC_pos : (0 : ℝ) < SC := by norm_num [SC]

/-! ### Anchors -/

theorem nat_le_mul_ceilDiv (x a : ℕ) (ha : 0 < a) : x ≤ a * ((x + (a - 1)) / a) := by
  have h1 := Nat.div_add_mod (x + (a - 1)) a
  have h2 := Nat.mod_lt (x + (a - 1)) ha
  generalize a * ((x + (a - 1)) / a) = T at h1 ⊢
  omega

theorem expPoly_eq (U : ℕ) :
    (expPoly U : ℝ) = 40320 * (SC : ℝ) ^ 8 * ∑ i ∈ range 9, ((U : ℝ) / SC) ^ i / (Nat.factorial i : ℝ) := by
  have hSC : (SC : ℝ) ≠ 0 := SC_pos.ne'
  simp only [expPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  simp only [Nat.factorial, Nat.succ_eq_add_one]
  push_cast
  field_simp
  ring

theorem log_le_of_expCheck {a b U : ℕ} (ha : 0 < a) (h : expCheck a b U = true) :
    Real.log b ≤ Real.log a + U / SC := by
  have hK : (0 : ℝ) < 40320 * (SC : ℝ) ^ 8 := by have := SC_pos; positivity
  have hb' : (b : ℝ) * (40320 * (SC : ℝ) ^ 8) ≤ a * (expPoly U : ℝ) := by
    have := Nat.le_of_ble_eq_true h
    exact_mod_cast this
  rw [expPoly_eq] at hb'
  set x : ℝ := (U : ℝ) / SC
  have hx0 : 0 ≤ x := by have := SC_pos; positivity
  have hsum := Real.sum_le_exp_of_nonneg hx0 9
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hba : (b : ℝ) ≤ a * Real.exp x := by
    have h1 : (b : ℝ) ≤ a * ∑ i ∈ range 9, x ^ i / (Nat.factorial i : ℝ) := by
      have : (b : ℝ) * (40320 * (SC : ℝ) ^ 8) ≤
          (a * ∑ i ∈ range 9, x ^ i / (Nat.factorial i : ℝ)) * (40320 * (SC : ℝ) ^ 8) := by
        calc (b : ℝ) * (40320 * (SC : ℝ) ^ 8)
            ≤ a * (40320 * (SC : ℝ) ^ 8 * ∑ i ∈ range 9, x ^ i / (Nat.factorial i : ℝ)) := hb'
          _ = (a * ∑ i ∈ range 9, x ^ i / (Nat.factorial i : ℝ)) * (40320 * (SC : ℝ) ^ 8) := by ring
      exact le_of_mul_le_mul_right this hK
    calc (b : ℝ) ≤ a * ∑ i ∈ range 9, x ^ i / (Nat.factorial i : ℝ) := h1
      _ ≤ a * Real.exp x := by gcongr
  rcases Nat.eq_zero_or_pos b with hb0 | hb0
  · subst hb0
    have : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · have hb'' : (0 : ℝ) < b := by exact_mod_cast hb0
    calc Real.log b ≤ Real.log (a * Real.exp x) := Real.log_le_log hb'' hba
      _ = Real.log a + x := by
        rw [Real.log_mul ha'.ne' (Real.exp_pos x).ne', Real.log_exp]

/-- The property every anchor has. -/
def AnchorGood (p : ℕ × ℕ) : Prop := 2 ≤ p.1 ∧ Real.log p.1 ≤ p.2 / SC

theorem chainOK_good : ∀ (L : List (ℕ × ℕ)) (x : ℕ × ℕ), chainOK (x :: L) = true →
    AnchorGood x → ∀ y ∈ x :: L, AnchorGood y := by
  intro L
  induction L with
  | nil =>
    intro x _ hx y hy
    simp only [List.mem_singleton] at hy
    exact hy ▸ hx
  | cons z L ih =>
    intro x h hx y hy
    obtain ⟨a, l⟩ := x
    obtain ⟨b, l'⟩ := z
    simp only [chainOK, pairOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨hab, hll⟩, hexp⟩, hrest⟩ := h
    have hz : AnchorGood (b, l') := by
      obtain ⟨ha2, hal⟩ := hx
      refine ⟨by simp only at ha2 ⊢; omega, ?_⟩
      simp only at ha2 hal ⊢
      have h1 := log_le_of_expCheck (by omega) hexp
      have h2 : ((l' - l : ℕ) : ℝ) = (l' : ℝ) - l := by push_cast [hll]; ring
      rw [h2] at h1
      calc Real.log b ≤ Real.log a + ((l' : ℝ) - l) / SC := h1
        _ ≤ l / SC + ((l' : ℝ) - l) / SC := by linarith
        _ = l' / SC := by ring
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact ih (b, l') hrest hz y hy

theorem log_two_le : Real.log 2 ≤ (693147180800000 : ℕ) / SC := by
  have := Real.log_two_lt_d9
  norm_num [SC] at this ⊢
  linarith

theorem anchor_good {p : ℕ × ℕ} (hp : p ∈ anchorsAll) : AnchorGood p := by
  obtain ⟨t, ht⟩ : ∃ t, anchorsAll = (2, 693147180800000) :: t := by
    have h := anchors_head
    cases hL : anchorsAll with
    | nil => rw [hL] at h; simp at h
    | cons x t => rw [hL] at h; simp only [List.head?_cons, Option.some.injEq] at h; exact ⟨t, h ▸ rfl⟩
  rw [ht] at hp
  have hc := anchors_chainOK
  rw [ht] at hc
  exact chainOK_good t _ hc ⟨le_rfl, by exact_mod_cast log_two_le⟩ p hp

theorem anchorOf_mem {i : ℕ} (h : (anchorOf i).1 ≠ 0) : anchorOf i ∈ anchorsAll := by
  unfold anchorOf at h ⊢
  by_cases hi : i < anchorsAll.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (by omega)] at h
    simp at h

/-! ### The weight -/

theorem log_le_weight {n a l : ℕ} (ha : 2 ≤ a) (han : a ≤ n) (hl : Real.log a ≤ l / SC) :
    Real.log n ≤ weight n a l / SC := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set c := ((n - a) * SC + (a - 1)) / a with hc
  have hcN : (n - a) * SC ≤ a * c := nat_le_mul_ceilDiv _ _ (by omega)
  have hw : (weight n a l : ℝ) = l + c := by
    have : weight n a l = l + c := rfl
    rw [this]
    push_cast
    ring
  have h1 : Real.log n - Real.log a ≤ ((n : ℝ) - a) / a := by
    rw [← Real.log_div hn'.ne' ha'.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hn' ha')
    calc Real.log (n / a) ≤ n / a - 1 := this
      _ = ((n : ℝ) - a) / a := by field_simp
  have h2 : ((n : ℝ) - a) / a ≤ c / SC := by
    rw [div_le_div_iff₀ ha' SC_pos]
    have : (((n - a) * SC : ℕ) : ℝ) ≤ ((a * c : ℕ) : ℝ) := by exact_mod_cast hcN
    push_cast [han] at this
    linarith
  rw [hw]
  calc Real.log n ≤ Real.log a + ((n : ℝ) - a) / a := by linarith
    _ ≤ l / SC + c / SC := by linarith
    _ = (l + c) / SC := by ring

/-! ### Possible primes -/

theorem trialAux_succ (n f d : ℕ) :
    trialAux n (f + 1) d =
      (match Nat.blt n (Nat.mul d d) with
      | true => true
      | false =>
        match Nat.beq (Nat.mod n d) 0 with
        | true => false
        | false => trialAux n f (Nat.succ d)) := rfl

theorem trialAux_prime {n : ℕ} (hn : n.Prime) : ∀ f d, 2 ≤ d → trialAux n f d = true := by
  intro f
  induction f with
  | zero => intro d _; rfl
  | succ f ih =>
    intro d hd
    rw [trialAux_succ]
    cases h1 : Nat.blt n (Nat.mul d d) with
    | true => rfl
    | false =>
      have hdd : d * d ≤ n := by
        by_contra hc
        have : Nat.blt n (Nat.mul d d) = true := Nat.blt_eq.mpr (Nat.lt_of_not_le hc)
        rw [this] at h1
        exact absurd h1 (by decide)
      cases h2 : Nat.beq (Nat.mod n d) 0 with
      | true =>
        exfalso
        have h2' : n % d = 0 := Nat.eq_of_beq_eq_true h2
        have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2'
        rcases (Nat.dvd_prime hn).mp hdvd with h | h
        · omega
        · subst h
          have := hn.two_le
          nlinarith
      | false => exact ih (d + 1) (by omega)

theorem isSurv_prime {n : ℕ} (hn : n.Prime) : isSurv n = true := by
  unfold isSurv
  cases h : Nat.ble n 5000 with
  | true => exact trialAux_prime hn n 2 le_rfl
  | false =>
    have h5 : 5000 < n := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h
      exact absurd h (by decide)
    have hg : Nat.gcd n bigP = 1 := by
      rw [← bigP_eq]
      show Nat.Coprime n smallD.prod
      rw [Nat.coprime_list_prod_right_iff]
      intro m hm
      have hm5 := smallD_le m hm
      have hm2 : 2 ≤ m := by
        simp only [smallD, List.mem_filter, Bool.and_eq_true, Nat.ble_eq] at hm
        exact hm.2.1
      rw [Nat.Prime.coprime_iff_not_dvd hn]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    show Nat.beq (Nat.gcd n bigP) 1 = true
    rw [hg]
    rfl

theorem prime_mem_smallD {p : ℕ} (hp : p.Prime) (h5 : p ≤ 5000) : p ∈ smallD := by
  simp only [smallD, List.mem_filter, List.mem_range, Bool.and_eq_true, Nat.ble_eq]
  exact ⟨by omega, hp.two_le, trialAux_prime hp p 2 le_rfl⟩

/-! ### Events -/

theorem sortedStrict_pairwise : ∀ L : List (ℕ × ℕ), sortedStrict L = true →
    L.Pairwise (fun x y => x.1 < y.1) := by
  intro L
  induction L with
  | nil => intro _; exact List.Pairwise.nil
  | cons x L ih =>
    intro h
    cases L with
    | nil => exact List.pairwise_singleton _ _
    | cons y L =>
      simp only [sortedStrict, Bool.and_eq_true, Nat.blt_eq] at h
      have hp := ih h.2
      refine List.Pairwise.cons ?_ hp
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h.1
      · exact lt_trans h.1 ((List.pairwise_cons.mp hp).1 z hz)

theorem eventOf_lt {i j : ℕ} (hij : i < j) (hj : j < eventsAll.length) :
    (eventOf i).1 < (eventOf j).1 := by
  have hp := sortedStrict_pairwise _ events_sortedStrict
  rw [List.pairwise_iff_getElem] at hp
  unfold eventOf
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  exact hp i j (by omega) hj hij

theorem eventOf_out {i : ℕ} (hi : eventsAll.length ≤ i) : eventOf i = (0, 0) := by
  unfold eventOf
  exact List.getD_eq_default _ _ hi

theorem event_mem {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hpk : p ^ k ≤ NMAX) :
    ∃ j < eventsAll.length, eventOf j = (p ^ k, k) := by
  have hp5 : p ≤ 5000 := by
    have h2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    have : p * p ≤ 25000000 := by simpa [NMAX, sq] using h2.trans hpk
    nlinarith
  have hk25 : k < 25 := by
    by_contra hk'
    have h1 : 2 ^ 25 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
    have : 2 ^ 25 ≤ NMAX := h1.trans (h2.trans hpk)
    norm_num [NMAX] at this
  have hc := events_complete
  simp only [eventsComplete, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, List.contains_iff_mem] at hc
  have hmem := hc p (prime_mem_smallD hp hp5) k hk25
  have hmem' : (p ^ k, k) ∈ eventsAll := by
    rcases hmem with (h | h) | h
    · rw [Nat.ble_eq_true_of_le hk] at h; exact absurd h (by decide)
    · rw [Nat.ble_eq_true_of_le hpk] at h; exact absurd h (by decide)
    · exact h
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem'
  refine ⟨j, hj, ?_⟩
  unfold eventOf
  rw [List.getD_eq_getElem _ _ hj, hjeq]

end RSBounds.HelfgottSmall
