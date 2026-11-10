import RSBounds.HelfgottSmall.Analysis

/-!
# Soundness of the walk

`walk_inv`: a successful walk keeps the invariant `Inv` (its scaled sums bound
`∑_{m < n} Λ(m)` and `∑_{m < n} Λ(m) m`), and at every position it passed, the checks give
[H] (2.14) and (2.17) there (`GoodAt`).
-/

namespace RSBounds.HelfgottSmall

open Real Finset ArithmeticFunction

/-- `∑_{1 ≤ m ≤ n} Λ(m)`, that is `ψ(n)`. -/
noncomputable def psiS (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, (Λ m : ℝ)

/-- `∑_{1 ≤ m ≤ n} Λ(m) m`. -/
noncomputable def sS (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, (Λ m : ℝ) * m

/-- (2.14) and (2.17) at the integer `m`, where they apply. -/
def GoodAt (m : ℕ) : Prop :=
  (2000000 ≤ m → m ≤ 4000000 → psiS m ≤ 1.0004 * m) ∧
  (1600000 ≤ m → m ≤ 25000000 → sS m < 1.0008 * (m : ℝ) ^ 2 / 2)

/-- The walk's invariant. -/
def Inv : St → Prop
  | (n, psi, s, ia, a, l, b, ie, q, k) =>
    2 ≤ n ∧ psiS (n - 1) ≤ psi / SC ∧ sS (n - 1) ≤ s / SC ∧ (a, l) ∈ anchorsAll ∧
      b = (anchorOf (ia + 1)).1 ∧ (q, k) = eventOf ie ∧ (n ≤ q ∨ eventsAll.length ≤ ie) ∧
      ∀ j < ie, (eventOf j).1 < n

/-- The increment the walk adds at `n`. -/
def incOf (n a l q k : ℕ) : ℕ :=
  Nat.add (match isSurv n with | true => weight n a l | false => 0)
    (match Nat.beq q n with
      | true => Nat.div (Nat.sub (Nat.add (weight n a l) k) 1) k
      | false => 0)

theorem weight_le_incOf {n a l q k : ℕ} (hs : isSurv n = true) :
    weight n a l ≤ incOf n a l q k := by
  unfold incOf
  rw [hs]
  exact Nat.le_add_right _ _

theorem ceil_le_incOf {n a l k : ℕ} :
    (weight n a l + k - 1) / k ≤ incOf n a l n k := by
  unfold incOf
  rw [Nat.beq_refl]
  exact Nat.le_add_left _ _

theorem vonMangoldt_le_inc {n a l ie q k : ℕ} (hnN : n ≤ NMAX) (ha : 2 ≤ a) (han : a ≤ n)
    (hl : Real.log a ≤ l / SC) (hqk : (q, k) = eventOf ie) (hq : n ≤ q ∨ eventsAll.length ≤ ie)
    (hprev : ∀ j < ie, (eventOf j).1 < n) :
    (Λ n : ℝ) ≤ (incOf n a l q k : ℝ) / SC := by
  have hSC := SC_pos
  have hinc0 : (0 : ℝ) ≤ (incOf n a l q k : ℝ) / SC := by positivity
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, e, hp, he, hpe⟩ := isPrimePow_nat_iff n |>.mp hpp
    have hΛ : (Λ n : ℝ) = Real.log p := by
      rw [← hpe, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    have hw := log_le_weight ha han hl
    set w := weight n a l
    rcases Nat.lt_or_ge e 2 with he1 | he2
    · have he1 : e = 1 := by omega
      subst he1
      rw [pow_one] at hpe
      subst hpe
      have hs : isSurv p = true := isSurv_prime hp
      rw [hΛ]
      calc Real.log p ≤ w / SC := hw
        _ ≤ (incOf p a l q k : ℝ) / SC := by
          gcongr
          exact_mod_cast weight_le_incOf hs
    · obtain ⟨j, hj, hje⟩ := event_mem hp he2 (hpe ▸ hnN)
      have hje1 : (eventOf j).1 = n := by rw [hje, hpe]
      have hjie : j = ie := by
        rcases Nat.lt_trichotomy j ie with h | h | h
        · have := hprev j h; omega
        · exact h
        · have h1 := eventOf_lt h hj
          rw [← hqk] at h1
          simp only at h1
          rcases hq with hq | hq
          · omega
          · omega
      subst hjie
      rw [← hqk] at hje
      simp only [Prod.mk.injEq] at hje
      obtain ⟨hq', hk'⟩ := hje
      have hqn : q = n := by rw [hq', hpe]
      subst hk'
      subst hqn
      have he0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hlogp : Real.log p = Real.log q / k := by
        rw [← hpe]; push_cast; rw [Real.log_pow]; field_simp
      have hceil : (w : ℝ) / k ≤ ((w + k - 1) / k : ℕ) := by
        rw [div_le_iff₀ he0]
        have := nat_le_mul_ceilDiv w k (by omega)
        have h' : w + k - 1 = w + (k - 1) := by omega
        rw [h']
        calc (w : ℝ) ≤ ((k * ((w + (k - 1)) / k) : ℕ) : ℝ) := by exact_mod_cast this
          _ = ((w + (k - 1)) / k : ℕ) * k := by push_cast; ring
      rw [hΛ, hlogp]
      calc Real.log q / k ≤ (w / SC) / k := by gcongr
        _ = ((w : ℝ) / k) / SC := by ring
        _ ≤ (((w + k - 1) / k : ℕ) : ℝ) / SC := by gcongr
        _ ≤ (incOf q a l q k : ℝ) / SC := by
          gcongr
          exact_mod_cast ceil_le_incOf
  · have : (Λ n : ℝ) = 0 := by
      rw [vonMangoldt_apply, ite_eq_right_iff.mpr (fun h => absurd h hpp)]
    rw [this]
    exact hinc0

/-! ### One step -/

theorem stepB_some {n psi s ia a l b ie q k inc : ℕ} {st' : St}
    (h : stepB n psi s ia a l b ie q k inc = some st') :
    st' = (n + 1, psi + inc, s + n * inc, ia, a, l, b, ie, q, k) ∧
      check14 n (psi + inc) = true ∧ check17 n (s + n * inc) = true := by
  unfold stepB at h
  simp only [force_eq] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    simp only [Option.some.injEq] at h
    exact ⟨h.symm, hc.1, hc.2⟩

theorem stepA_some {n psi s ia a l b ie q k : ℕ} {st' : St}
    (h : stepA n psi s ia a l b ie q k = some st') :
    a ≤ n ∧ 2 ≤ a ∧ n ≤ NMAX ∧
      ((q = n ∧ stepB n psi s ia a l b (Nat.succ ie) (eventOf (Nat.succ ie)).1
          (eventOf (Nat.succ ie)).2 (incOf n a l q k) = some st') ∨
        (q ≠ n ∧ stepB n psi s ia a l b ie q k (incOf n a l q k) = some st')) := by
  unfold stepA at h
  split at h
  · exact absurd h (by simp)
  · rename_i hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at hg
    obtain ⟨⟨han, ha2⟩, hnN⟩ := hg
    refine ⟨han, ha2, hnN, ?_⟩
    split at h
    · rename_i hq
      have hq' : q = n := Nat.eq_of_beq_eq_true hq
      left
      refine ⟨hq', ?_⟩
      simp only [force_eq] at h
      have e : incOf n a l q k = Nat.add (match isSurv n with | true => weight n a l | false => 0)
          (Nat.div (Nat.sub (Nat.add (weight n a l) k) 1) k) := by
        unfold incOf
        rw [hq]
      rw [e]
      exact h
    · rename_i hq
      have hq' : q ≠ n := fun e => by rw [e, Nat.beq_refl] at hq; exact absurd hq (by decide)
      right
      refine ⟨hq', ?_⟩
      split at h
      · rename_i hs
        simp only [force_eq] at h
        have e : incOf n a l q k = weight n a l := by
          unfold incOf
          rw [hs, hq]
          exact Nat.add_zero _
        rw [e]
        exact h
      · rename_i hs
        have e : incOf n a l q k = 0 := by
          unfold incOf
          rw [hs, hq]
          rfl
        rw [e]
        exact h

theorem check14_spec {n psi : ℕ} (h : check14 n psi = true) (h1 : 2000000 ≤ n)
    (h2 : n ≤ 4000000) : (psi : ℝ) / SC ≤ 1.0004 * n := by
  unfold check14 at h
  have hr : (Nat.ble 2000000 n && Nat.ble n 4000000) = true := by
    simp [Nat.ble_eq, h1, h2]
  rw [hr] at h
  have h' : 10000 * psi ≤ 10004 * n * SC := Nat.le_of_ble_eq_true h
  have h'' : (10000 : ℝ) * psi ≤ 10004 * n * SC := by exact_mod_cast h'
  rw [div_le_iff₀ SC_pos]
  linarith

theorem check17_spec {n s : ℕ} (h : check17 n s = true) (h1 : 1600000 ≤ n)
    (h2 : n ≤ 25000000) : (s : ℝ) / SC < 1.0008 * (n : ℝ) ^ 2 / 2 := by
  unfold check17 at h
  have hr : (Nat.ble 1600000 n && Nat.ble n 25000000) = true := by
    simp [Nat.ble_eq, h1, h2]
  rw [hr] at h
  have h' : 20000 * s < 10008 * n * n * SC := Nat.blt_eq.mp h
  have h'' : (20000 : ℝ) * s < 10008 * n * n * SC := by exact_mod_cast h'
  rw [div_lt_iff₀ SC_pos]
  nlinarith

theorem psiS_succ (n : ℕ) : psiS (n + 1) = psiS n + Λ (n + 1) := by
  unfold psiS
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem sS_succ (n : ℕ) : sS (n + 1) = sS n + Λ (n + 1) * (n + 1 : ℕ) := by
  unfold sS
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- The heart of a step, once the anchor `(a, l)` and `b` are fixed. -/
theorem stepA_inv {n psi s ia a l b ie q k : ℕ} {st' : St}
    (hn : 2 ≤ n) (hpsi : psiS (n - 1) ≤ psi / SC) (hs : sS (n - 1) ≤ s / SC)
    (hmem : (a, l) ∈ anchorsAll) (hb : b = (anchorOf (ia + 1)).1)
    (hqk : (q, k) = eventOf ie) (hq : n ≤ q ∨ eventsAll.length ≤ ie)
    (hprev : ∀ j < ie, (eventOf j).1 < n)
    (h : stepA n psi s ia a l b ie q k = some st') :
    Inv st' ∧ st'.1 = n + 1 ∧ GoodAt n := by
  obtain ⟨han, ha2, hnN, hbr⟩ := stepA_some h
  have hl := (anchor_good hmem).2
  have hΛ := vonMangoldt_le_inc hnN ha2 han hl hqk hq hprev
  set inc := incOf n a l q k
  have hSC := SC_pos
  have hn1 : n - 1 + 1 = n := by omega
  have hpsi' : psiS n ≤ ((psi + inc : ℕ) : ℝ) / SC := by
    rw [← hn1, psiS_succ, hn1]
    push_cast
    rw [add_div]
    linarith
  have hs' : sS n ≤ ((s + n * inc : ℕ) : ℝ) / SC := by
    rw [← hn1, sS_succ, hn1]
    push_cast
    rw [add_div]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have : (Λ n : ℝ) * n ≤ (n : ℝ) * inc / SC := by
      calc (Λ n : ℝ) * n ≤ (inc : ℝ) / SC * n := by gcongr
        _ = (n : ℝ) * inc / SC := by ring
    linarith
  have good : ∀ psi' s' : ℕ, psi' = psi + inc → s' = s + n * inc →
      check14 n psi' = true → check17 n s' = true → GoodAt n := by
    intro psi' s' hp hs hc14 hc17
    subst hp hs
    refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
    · exact hpsi'.trans (check14_spec hc14 h1 h2)
    · exact lt_of_le_of_lt hs' (check17_spec hc17 h1 h2)
  rcases hbr with ⟨hqn, hB⟩ | ⟨hqn, hB⟩
  · obtain ⟨rfl, hc14, hc17⟩ := stepB_some hB
    refine ⟨⟨by omega, by simpa using hpsi', by simpa using hs', hmem, hb, Prod.mk.eta, ?_, ?_⟩,
      rfl, good _ _ rfl rfl hc14 hc17⟩
    · by_cases hlen : ie + 1 < eventsAll.length
      · left
        have := eventOf_lt (Nat.lt_succ_self ie) hlen
        rw [← hqk] at this
        simp only at this
        omega
      · right; omega
    · intro j hj
      rcases Nat.lt_or_ge j ie with hj' | hj'
      · have := hprev j hj'; omega
      · have : j = ie := by omega
        subst this
        rw [← hqk]
        simp only
        omega
  · obtain ⟨rfl, hc14, hc17⟩ := stepB_some hB
    refine ⟨⟨by omega, by simpa using hpsi', by simpa using hs', hmem, hb, hqk, ?_, ?_⟩, rfl,
      good _ _ rfl rfl hc14 hc17⟩
    · rcases hq with hq | hq
      · left; omega
      · right; exact hq
    · intro j hj
      have := hprev j hj
      omega

theorem step_eq (n psi s ia a l b ie q k : ℕ) :
    step (n, psi, s, ia, a, l, b, ie, q, k) =
      (match Nat.beq n b with
      | true =>
        force (anchorOf (Nat.succ ia)).2 fun l' =>
        force (anchorOf (Nat.succ (Nat.succ ia))).1 fun b' =>
        stepA n psi s (Nat.succ ia) b l' b' ie q k
      | false => stepA n psi s ia a l b ie q k) := rfl

theorem step_inv {st st' : St} (hI : Inv st) (h : step st = some st') :
    Inv st' ∧ st'.1 = st.1 + 1 ∧ GoodAt st.1 := by
  obtain ⟨n, psi, s, ia, a, l, b, ie, q, k⟩ := st
  obtain ⟨hn, hpsi, hs, hmem, hb, hqk, hq, hprev⟩ := hI
  rw [step_eq] at h
  split at h
  · rename_i hnb
    have hnb' : n = b := Nat.eq_of_beq_eq_true hnb
    simp only [force_eq] at h
    have hmem' : (b, (anchorOf (ia + 1)).2) ∈ anchorsAll := by
      have hne : (anchorOf (ia + 1)).1 ≠ 0 := by rw [← hb, ← hnb']; omega
      have := anchorOf_mem hne
      rw [hb]
      exact this
    exact stepA_inv hn hpsi hs hmem' rfl hqk hq hprev h
  · exact stepA_inv hn hpsi hs hmem hb hqk hq hprev h

theorem walk_succ (f : ℕ) (st : St) :
    walk (f + 1) st = (match step st with
      | none => none
      | some st' => walk f st') := rfl

theorem walk_inv : ∀ (f : ℕ) (st st' : St), Inv st → walk f st = some st' →
    Inv st' ∧ st'.1 = st.1 + f ∧ ∀ m, st.1 ≤ m → m < st.1 + f → GoodAt m := by
  intro f
  induction f with
  | zero =>
    intro st st' hI h
    have h0 : walk 0 st = some st := rfl
    rw [h0, Option.some.injEq] at h
    subst h
    exact ⟨hI, rfl, fun m h1 h2 => by omega⟩
  | succ f ih =>
    intro st st' hI h
    rw [walk_succ] at h
    split at h
    · exact absurd h (by simp)
    · rename_i st'' hst
      obtain ⟨hI'', hn'', hgood⟩ := step_inv hI hst
      obtain ⟨hI', hn', hgood'⟩ := ih st'' st' hI'' h
      refine ⟨hI', by omega, fun m h1 h2 => ?_⟩
      rcases Nat.lt_or_ge m (st.1 + 1) with hm | hm
      · have : m = st.1 := by omega
        exact this ▸ hgood
      · exact hgood' m (by omega) (by omega)

theorem stEq_eq {r st : St} (h : stEq r st = true) : r = st := by
  obtain ⟨n, psi, s, ia, a, l, b, ie, q, k⟩ := r
  obtain ⟨n', psi', s', ia', a', l', b', ie', q', k'⟩ := st
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

theorem walk_of_chunkOK {f : ℕ} {st st' : St} (h : chunkOK f st st' = true) :
    walk f st = some st' := by
  unfold chunkOK at h
  split at h
  · rename_i r hr
    rw [hr, stEq_eq h]
  · exact absurd h (by simp)

end RSBounds.HelfgottSmall
