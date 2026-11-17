import RSBounds.HelfgottLow.Analysis

/-!
# Soundness of the walk

`walk_inv`: a successful walk keeps the invariant `Inv` (its scaled sums bound the sums they stand
for), and at every position it passed, the checks give [H] (2.16), (2.18) and (2.19) there
(`GoodAt`).
-/

namespace RSBounds.HelfgottLow

open Real Finset ArithmeticFunction
open RSBounds.HelfgottSmall (SC SC_pos isSurv weight force force_eq eventOf eventsAll incOf psiS sS
  psiS_succ sS_succ vonMangoldt_le_inc log_le_weight isSurv_prime eventOf_lt NMAX)

/-! ### The sums -/

/-- `∑_{1 ≤ m ≤ n} Λ(m) / √m`. -/
noncomputable def tS (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, (Λ m : ℝ) / √(m : ℝ)

/-- `∑_{1 ≤ m ≤ n} Λ(m) (1 / √m - RHO0 / SC)`. -/
noncomputable def bS (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, (Λ m : ℝ) * (1 / √(m : ℝ) - RHO0 / SC)

/-- `(log m)²` if `m` may be prime, else `0`. -/
noncomputable def gS (m : ℕ) : ℝ := if isSurv m = true then Real.log m ^ 2 else 0

/-- `∑_{h < m ≤ N} gS(m)`. -/
noncomputable def wS (h N : ℕ) : ℝ := ∑ m ∈ Ioc h N, gS m

/-- (2.16), (2.18) and (2.19) at the integer `m`, where they apply. -/
def GoodAt (m : ℕ) : Prop :=
  (663 ≤ m → m ≤ 1600000 → sS m < 1.03884 * (m : ℝ) ^ 2 / 2) ∧
  tS m < 2.0008 * √(m : ℝ) ∧
  (117 ≤ m → ∑ p ∈ (Ioc (m / 2) m).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * m * Real.log m)

/-- The lower bound of the lagging pointer's anchor. -/
def LoGood (a lo : ℕ) : Prop := 2 ≤ a ∧ (lo : ℝ) / SC ≤ Real.log a

/-- The walk's invariant. -/
def Inv (st : St) : Prop :=
  2 ≤ st.n ∧ psiS (st.n - 1) ≤ st.psi / SC ∧ sS (st.n - 1) ≤ st.s / SC ∧
    tS (st.n - 1) ≤ st.t / SC ∧
    bS (st.n - 1) ≤ (st.t : ℝ) / SC - RHO0 / SC * (st.psi / SC) ∧
    wS ((st.n - 1) / 2) (st.n - 1) ≤ st.d / (SC : ℝ) ^ 2 ∧
    Good (st.a, st.l, st.lo, st.r) ∧ (∀ x ∈ st.ra, Good x) ∧
    LoGood st.aL st.loL ∧ (∀ x ∈ st.rl, Good x) ∧
    (st.q, st.k) = eventOf st.ie ∧ (st.n ≤ st.q ∨ eventsAll.length ≤ st.ie) ∧
    ∀ j < st.ie, (eventOf j).1 < st.n

/-! ### What a step computes -/

/-- What is added to `d` at `n`. -/
def addOf (n a l : ℕ) : ℕ :=
  match isSurv n with
  | true => Nat.mul (weight n a l) (weight n a l)
  | false => 0

/-- `d` after removing `m` from the window. -/
def lagD (m aL loL d : ℕ) : ℕ :=
  match isSurv m with
  | true => Nat.sub d (Nat.mul (lowW m aL loL) (lowW m aL loL))
  | false => d

theorem stepC_some {n psi s t d ia a l lo r b : ℕ} {ra : List Anc} {ja aL loL bL : ℕ}
    {rl : List Anc} {ie q k : ℕ} {st' : St}
    (h : stepC n psi s t d ia a l lo r b ra ja aL loL bL rl ie q k = some st') :
    st' = ⟨n + 1, psi, s, t, d, ia, a, l, lo, r, b, ra, ja, aL, loL, bL, rl, ie, q, k⟩ ∧
      check16 n s = true ∧ check18 n t = true ∧ check19 n d a lo = true := by
  unfold stepC at h
  split at h
  · exact absurd h (by simp)
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    rw [force_eq] at h
    simp only [Option.some.injEq] at h
    exact ⟨h.symm, hc.1.1, hc.1.2, hc.2⟩

theorem stepL_some {n psi s t d ia a l lo r b : ℕ} {ra : List Anc} {m ja aL loL bL : ℕ}
    {rl : List Anc} {ie q k : ℕ} {st' : St}
    (h : stepL n psi s t d ia a l lo r b ra m ja aL loL bL rl ie q k = some st') :
    aL ≤ m ∧ 2 ≤ aL ∧
      stepC n psi s t (lagD m aL loL d) ia a l lo r b ra ja aL loL bL rl ie q k = some st' := by
  unfold stepL at h
  split at h
  · exact absurd h (by simp)
  · rename_i hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at hg
    refine ⟨hg.1, hg.2, ?_⟩
    split at h
    · rename_i hs
      rw [force_eq, force_eq] at h
      unfold lagD
      rw [hs]
      exact h
    · rename_i hs
      unfold lagD
      rw [hs]
      exact h

theorem stepB_some {n psi s t d ia a l lo r b : ℕ} {ra : List Anc} {ja aL loL bL : ℕ}
    {rl : List Anc} {ie q k inc add : ℕ} {st' : St}
    (h : stepB n psi s t d ia a l lo r b ra ja aL loL bL rl ie q k inc add = some st') :
    ∃ ja' aL' loL' bL' rl' d',
      (LoGood aL loL → (∀ x ∈ rl, Good x) → LoGood aL' loL' ∧ ∀ x ∈ rl', Good x) ∧
      ((n % 2 = 0 ∧ 4 ≤ n ∧ aL' ≤ n / 2 ∧ d' = lagD (n / 2) aL' loL' (d + add)) ∨
        (¬ (n % 2 = 0 ∧ 4 ≤ n) ∧ d' = d + add)) ∧
      stepC n (psi + inc) (s + n * inc) (tNext n a r t inc) d' ia a l lo r b ra ja' aL' loL' bL'
        rl' ie q k = some st' := by
  unfold stepB at h
  simp only [force_eq] at h
  cases hc : (Nat.beq (Nat.mod n 2) 0 && Nat.ble 4 n) with
  | false =>
    rw [hc] at h
    refine ⟨ja, aL, loL, bL, rl, d + add, fun h1 h2 => ⟨h1, h2⟩, Or.inr ⟨?_, rfl⟩, h⟩
    rintro ⟨h1, h2⟩
    have h1' : Nat.mod n 2 = 0 := h1
    rw [h1', Nat.ble_eq_true_of_le h2] at hc
    exact absurd hc (by decide)
  | true =>
    rw [hc] at h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hc
    have hc1 : n % 2 = 0 := hc.1
    cases hm : Nat.beq (Nat.div n 2) bL with
    | false =>
      rw [hm] at h
      obtain ⟨hL1, hL2, hC⟩ := stepL_some h
      exact ⟨ja, aL, loL, bL, rl, _, fun h1 h2 => ⟨h1, h2⟩, Or.inl ⟨hc1, hc.2, hL1, rfl⟩, hC⟩
    | true =>
      rw [hm] at h
      cases rl with
      | nil => exact absurd h (by simp)
      | cons x rl' =>
        obtain ⟨aL', l'', loL', r''⟩ := x
        simp only at h
        obtain ⟨hL1, hL2, hC⟩ := stepL_some h
        refine ⟨ja + 1, aL', loL', _, rl', _, fun _ h2 => ?_, Or.inl ⟨hc1, hc.2, hL1, rfl⟩, hC⟩
        have hx : Good (aL', l'', loL', r'') := h2 _ List.mem_cons_self
        have hrl : ∀ y ∈ rl', Good y := fun y hy => h2 y (List.mem_cons_of_mem _ hy)
        obtain ⟨⟨hx2, _, hxlo⟩, _⟩ := hx
        exact ⟨⟨hx2, hxlo⟩, hrl⟩

theorem stepA_some {n psi s t d ia a l lo r b : ℕ} {ra : List Anc} {ja aL loL bL : ℕ}
    {rl : List Anc} {ie q k : ℕ} {st' : St}
    (h : stepA n psi s t d ia a l lo r b ra ja aL loL bL rl ie q k = some st') :
    a ≤ n ∧ 2 ≤ a ∧ n ≤ N0 ∧ ∃ ie' q' k',
      ((q = n ∧ ie' = ie + 1 ∧ (q', k') = eventOf (ie + 1)) ∨ (q ≠ n ∧ ie' = ie ∧ q' = q ∧ k' = k)) ∧
      stepB n psi s t d ia a l lo r b ra ja aL loL bL rl ie' q' k' (incOf n a l q k) (addOf n a l)
        = some st' := by
  unfold stepA at h
  split at h
  · exact absurd h (by simp)
  · rename_i hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at hg
    obtain ⟨⟨han, ha2⟩, hnN⟩ := hg
    refine ⟨han, ha2, hnN, ?_⟩
    split at h
    · rename_i hs
      have eadd : addOf n a l = Nat.mul (weight n a l) (weight n a l) := by
        unfold addOf; rw [hs]
      rw [force_eq] at h
      split at h
      · rename_i hq
        have hq' : q = n := Nat.eq_of_beq_eq_true hq
        simp only [force_eq] at h
        have einc : incOf n a l q k = Nat.add (weight n a l)
            (Nat.div (Nat.sub (Nat.add (weight n a l) k) 1) k) := by
          unfold incOf; rw [hs, hq]
        refine ⟨ie + 1, _, _, Or.inl ⟨hq', rfl, rfl⟩, ?_⟩
        rw [einc, eadd]
        exact h
      · rename_i hq
        have hq' : q ≠ n := fun e => by rw [e, Nat.beq_refl] at hq; exact absurd hq (by decide)
        have einc : incOf n a l q k = weight n a l := by
          unfold incOf; rw [hs, hq]; exact Nat.add_zero _
        refine ⟨ie, q, k, Or.inr ⟨hq', rfl, rfl, rfl⟩, ?_⟩
        rw [einc, eadd]
        exact h
    · rename_i hs
      have eadd : addOf n a l = 0 := by unfold addOf; rw [hs]
      split at h
      · rename_i hq
        have hq' : q = n := Nat.eq_of_beq_eq_true hq
        simp only [force_eq] at h
        have einc : incOf n a l q k = Nat.div (Nat.sub (Nat.add (weight n a l) k) 1) k := by
          unfold incOf; rw [hs, hq]; exact Nat.zero_add _
        refine ⟨ie + 1, _, _, Or.inl ⟨hq', rfl, rfl⟩, ?_⟩
        rw [einc, eadd]
        exact h
      · rename_i hq
        have hq' : q ≠ n := fun e => by rw [e, Nat.beq_refl] at hq; exact absurd hq (by decide)
        have einc : incOf n a l q k = 0 := by unfold incOf; rw [hs, hq]; rfl
        refine ⟨ie, q, k, Or.inr ⟨hq', rfl, rfl, rfl⟩, ?_⟩
        rw [einc, eadd]
        exact h

theorem step_some {n psi s t d ia a l lo r b : ℕ} {ra : List Anc} {ja aL loL bL : ℕ}
    {rl : List Anc} {ie q k : ℕ} {st' : St}
    (h : step ⟨n, psi, s, t, d, ia, a, l, lo, r, b, ra, ja, aL, loL, bL, rl, ie, q, k⟩ = some st') :
    ∃ ia' a' l' lo' r' b' ra',
      (Good (a, l, lo, r) → (∀ x ∈ ra, Good x) → Good (a', l', lo', r') ∧ ∀ x ∈ ra', Good x) ∧
      stepA n psi s t d ia' a' l' lo' r' b' ra' ja aL loL bL rl ie q k = some st' := by
  simp only [step] at h
  cases hnb : Nat.beq n b with
  | false =>
    rw [hnb] at h
    exact ⟨ia, a, l, lo, r, b, ra, fun h1 h2 => ⟨h1, h2⟩, h⟩
  | true =>
    rw [hnb] at h
    cases ra with
    | nil => exact absurd h (by simp)
    | cons x ra' =>
      obtain ⟨a', l', lo', r'⟩ := x
      simp only [force_eq] at h
      exact ⟨_, a', l', lo', r', _, ra', fun _ h2 => ⟨h2 _ List.mem_cons_self,
        fun y hy => h2 y (List.mem_cons_of_mem _ hy)⟩, h⟩

/-! ### The real-number content of a step -/

theorem check16_spec {n s : ℕ} (h : check16 n s = true) (h1 : 663 ≤ n) (h2 : n ≤ 1600000) :
    (s : ℝ) / SC < 1.03884 * (n : ℝ) ^ 2 / 2 := by
  unfold check16 at h
  have hr : (Nat.ble 663 n && Nat.ble n 1600000) = true := by simp [Nat.ble_eq, h1, h2]
  rw [hr] at h
  have h' : 200000 * s < 103884 * n * n * SC := Nat.blt_eq.mp h
  have h'' : (200000 : ℝ) * s < 103884 * n * n * SC := by exact_mod_cast h'
  rw [div_lt_iff₀ SC_pos]
  nlinarith

theorem check18_spec {n t : ℕ} (h : check18 n t = true) :
    (t : ℝ) / SC < 2.0008 * √(n : ℝ) := by
  unfold check18 at h
  have h' : 100000000 * t * t < 400320064 * n * SC * SC := Nat.blt_eq.mp h
  have h'' : (100000000 : ℝ) * t * t < 400320064 * n * SC * SC := by exact_mod_cast h'
  have hSC := SC_pos
  have hx0 : (0 : ℝ) ≤ (t : ℝ) / SC := by positivity
  have hsq : ((t : ℝ) / SC) ^ 2 < (2.0008 * √(n : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_pow, div_lt_iff₀ (by positivity)]
    nlinarith
  have hy0 : (0 : ℝ) ≤ 2.0008 * √(n : ℝ) := by positivity
  exact (pow_lt_pow_iff_left₀ hx0 hy0 (by norm_num)).mp hsq

theorem check19_spec {n D a lo : ℕ} (h : check19 n D a lo = true) (h1 : 117 ≤ n) (ha : 0 < a)
    (han : a ≤ n) (hlo : (lo : ℝ) / SC ≤ Real.log a) :
    (D : ℝ) / (SC : ℝ) ^ 2 ≤ 1 / 2 * n * Real.log n := by
  unfold check19 at h
  rw [Nat.ble_eq_true_of_le h1] at h
  have h' : 2 * D ≤ n * lowW n a lo * SC := Nat.le_of_ble_eq_true h
  have h'' : (2 : ℝ) * D ≤ n * lowW n a lo * SC := by exact_mod_cast h'
  have hw := lowW_le ha han hlo
  have hSC := SC_pos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (lowW n a lo : ℝ) ≤ SC * Real.log n := by
    rw [div_le_iff₀ hSC] at hw; linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ n * SC by positivity)]

theorem rho_le {n : ℕ} (hn : 0 < n) (hN : n ≤ N0 + 1) : (RHO0 : ℝ) / SC ≤ 1 / √(n : ℝ) := by
  have hSC := SC_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hv := Real.sqrt_pos.mpr hn'
  have h := rho0_ok
  have h' : (RHO0 : ℝ) * RHO0 * n ≤ SC * SC := by
    have : RHO0 * RHO0 * n ≤ SC * SC :=
      le_trans (Nat.mul_le_mul_left _ hN) h
    exact_mod_cast this
  rw [div_le_div_iff₀ hSC hv, one_mul]
  have hsq : ((RHO0 : ℝ) * √(n : ℝ)) ^ 2 ≤ (SC : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn'.le]; nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) hSC.le (by norm_num)).mp hsq

theorem tNext_spec {n a r t inc : ℕ} {L x : ℝ} (ha : 0 < a) (hn : 0 < n)
    (hr : SC * SC ≤ r * r * a) (hL0 : 0 ≤ L) (hL : L ≤ inc / SC)
    (hx : x ≤ 1 / √(n : ℝ)) :
    L * (1 / √(n : ℝ) - x) ≤ (tNext n a r t inc : ℝ) / SC - t / SC - x * (inc / SC) := by
  cases inc with
  | zero =>
    have : L = 0 := by simp at hL; linarith
    subst this
    simp [tNext]
  | succ j =>
    have e : tNext n a r t (j + 1) = t + incR n a r (j + 1) := rfl
    rw [e]
    have := incR_spec ha hn hr hL hx
    rw [Nat.cast_add, add_div]
    linarith

theorem tS_succ (n : ℕ) : tS (n + 1) = tS n + Λ (n + 1) / √((n + 1 : ℕ) : ℝ) := by
  unfold tS
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem bS_succ (n : ℕ) :
    bS (n + 1) = bS n + Λ (n + 1) * (1 / √((n + 1 : ℕ) : ℝ) - RHO0 / SC) := by
  unfold bS
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem wS_succ_top {h N : ℕ} (hN : h ≤ N) : wS h (N + 1) = wS h N + gS (N + 1) := by
  unfold wS
  exact Finset.sum_Ioc_succ_top hN _

theorem wS_succ_bot {h N : ℕ} (hN : h < N) : wS (h + 1) N = wS h N - gS (h + 1) := by
  unfold wS
  have := Finset.sum_Ioc_consecutive gS (Nat.le_succ h) (show h + 1 ≤ N by omega)
  rw [← this, Nat.Ioc_succ_singleton, Finset.sum_singleton]
  ring

theorem gS_one : gS 1 = 0 := by simp [gS]

theorem gS_le_addOf {n a l : ℕ} (ha : 2 ≤ a) (han : a ≤ n) (hl : Real.log a ≤ l / SC) :
    gS n ≤ addOf n a l / (SC : ℝ) ^ 2 := by
  unfold gS addOf
  cases hs : isSurv n with
  | false => simp
  | true =>
    simp only [ite_true]
    have hw := log_le_weight ha han hl
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hSC := SC_pos
    have : Real.log n ^ 2 ≤ ((weight n a l : ℝ) / SC) ^ 2 := by gcongr
    calc Real.log n ^ 2 ≤ ((weight n a l : ℝ) / SC) ^ 2 := this
      _ = ((Nat.mul (weight n a l) (weight n a l) : ℕ) : ℝ) / (SC : ℝ) ^ 2 := by
        rw [show Nat.mul (weight n a l) (weight n a l) = weight n a l * weight n a l from rfl]
        push_cast; ring

theorem lagD_spec {m aL loL D : ℕ} (ha : 2 ≤ aL) (ham : aL ≤ m)
    (hlo : (loL : ℝ) / SC ≤ Real.log aL) :
    (D : ℝ) / (SC : ℝ) ^ 2 - gS m ≤ lagD m aL loL D / (SC : ℝ) ^ 2 := by
  unfold gS lagD
  cases hs : isSurv m with
  | false => simp
  | true =>
    simp only [ite_true]
    have hSC := SC_pos
    have hv := lowW_le (by omega) ham hlo
    have hv0 : (0 : ℝ) ≤ (lowW m aL loL : ℝ) / SC := by positivity
    have hsq : ((lowW m aL loL : ℝ) / SC) ^ 2 ≤ Real.log m ^ 2 := by gcongr
    have hsub : (D : ℝ) - (lowW m aL loL : ℝ) * lowW m aL loL ≤
        ((Nat.sub D (Nat.mul (lowW m aL loL) (lowW m aL loL)) : ℕ) : ℝ) := by
      have : D - lowW m aL loL * lowW m aL loL ≥ D - lowW m aL loL * lowW m aL loL := le_rfl
      rcases le_or_gt (lowW m aL loL * lowW m aL loL) D with h | h
      · have e : ((Nat.sub D (Nat.mul (lowW m aL loL) (lowW m aL loL)) : ℕ) : ℝ) =
            (D : ℝ) - (lowW m aL loL : ℝ) * lowW m aL loL := by
          show ((D - lowW m aL loL * lowW m aL loL : ℕ) : ℝ) = _
          push_cast [h]; ring
        rw [e]
      · have : (D : ℝ) < (lowW m aL loL : ℝ) * lowW m aL loL := by exact_mod_cast h
        have : (0 : ℝ) ≤ ((Nat.sub D (Nat.mul (lowW m aL loL) (lowW m aL loL)) : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        linarith
    have e2 : ((lowW m aL loL : ℝ) / SC) ^ 2 = (lowW m aL loL : ℝ) * lowW m aL loL / (SC : ℝ) ^ 2 := by
      ring
    rw [e2] at hsq
    have : (D : ℝ) / (SC : ℝ) ^ 2 - (lowW m aL loL : ℝ) * lowW m aL loL / (SC : ℝ) ^ 2 ≤
        ((Nat.sub D (Nat.mul (lowW m aL loL) (lowW m aL loL)) : ℕ) : ℝ) / (SC : ℝ) ^ 2 := by
      rw [← sub_div]
      gcongr
    linarith

theorem primes_le_wS (m : ℕ) :
    ∑ p ∈ (Ioc (m / 2) m).filter Nat.Prime, Real.log p ^ 2 ≤ wS (m / 2) m := by
  unfold wS
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p _
  unfold gS
  split_ifs with hp hs hs
  · exact le_rfl
  · exact absurd (isSurv_prime hp) hs
  · exact sq_nonneg _
  · exact le_rfl

/-! ### One step -/

theorem step_inv {st st' : St} (hI : Inv st) (h : step st = some st') :
    Inv st' ∧ st'.n = st.n + 1 ∧ GoodAt st.n := by
  obtain ⟨n, psi, s, t, d, ia, a, l, lo, r, b, ra, ja, aL, loL, bL, rl, ie, q, k⟩ := st
  obtain ⟨hn, hpsi, hs, ht, hb, hw, hA, hra, hL, hrl, hqk, hq, hprev⟩ := hI
  simp only at hn hpsi hs ht hb hw hA hra hL hrl hqk hq hprev
  obtain ⟨ia', a', l', lo', r', b', ra', hgA, hA'⟩ := step_some h
  obtain ⟨hgA', hra'⟩ := hgA hA hra
  obtain ⟨han, ha2, hnN, ie', q', k', hev, hB⟩ := stepA_some hA'
  obtain ⟨ja', aL', loL', bL', rl', d', hgL, hlag, hC⟩ := stepB_some hB
  obtain ⟨hL', hrl'⟩ := hgL hL hrl
  obtain ⟨rfl, hc16, hc18, hc19⟩ := stepC_some hC
  obtain ⟨⟨_, hl, hlo⟩, hr⟩ := hgA'
  simp only at hl hlo hr
  have hΛ := vonMangoldt_le_inc (show n ≤ NMAX by unfold NMAX; unfold N0 at hnN; omega) ha2 han hl
    hqk hq hprev
  set inc := incOf n a' l' q k
  have hSC := SC_pos
  have hn1 : n - 1 + 1 = n := by omega
  have hΛ0 : (0 : ℝ) ≤ Λ n := by exact_mod_cast vonMangoldt_nonneg
  have hpsi' : psiS n ≤ ((psi + inc : ℕ) : ℝ) / SC := by
    rw [← hn1, psiS_succ, hn1]
    push_cast; rw [add_div]; linarith
  have hs' : sS n ≤ ((s + n * inc : ℕ) : ℝ) / SC := by
    rw [← hn1, sS_succ, hn1]
    push_cast; rw [add_div]
    have : (Λ n : ℝ) * n ≤ (n : ℝ) * inc / SC := by
      calc (Λ n : ℝ) * n ≤ (inc : ℝ) / SC * n := by gcongr
        _ = (n : ℝ) * inc / SC := by ring
    linarith
  have hn0 : 0 < n := by omega
  have hsqrt0 : (0 : ℝ) ≤ 1 / √(n : ℝ) := by positivity
  have ht' : tS n ≤ (tNext n a' r' t inc : ℝ) / SC := by
    have := tNext_spec (t := t) (by omega) hn0 hr hΛ0 hΛ (x := 0) hsqrt0
    rw [← hn1, tS_succ, hn1]
    have e : (Λ n : ℝ) / √(n : ℝ) = Λ n * (1 / √(n : ℝ) - 0) := by ring
    rw [e]
    linarith
  have hb' : bS n ≤ (tNext n a' r' t inc : ℝ) / SC - RHO0 / SC * (((psi + inc : ℕ) : ℝ) / SC) := by
    have hρ := rho_le hn0 (by omega)
    have := tNext_spec (t := t) (by omega) hn0 hr hΛ0 hΛ hρ
    rw [← hn1, bS_succ, hn1]
    push_cast
    rw [add_div]
    linarith
  -- the window
  have hwadd : wS ((n - 1) / 2) n ≤ ((d + addOf n a' l' : ℕ) : ℝ) / (SC : ℝ) ^ 2 := by
    have e := wS_succ_top (h := (n - 1) / 2) (N := n - 1) (by omega)
    rw [hn1] at e
    rw [e]
    have := gS_le_addOf ha2 han hl
    push_cast
    rw [add_div]
    linarith
  have hw' : wS (n / 2) n ≤ (d' : ℝ) / (SC : ℝ) ^ 2 := by
    rcases hlag with ⟨hev2, h4, hamL, rfl⟩ | ⟨hno, rfl⟩
    · have e1 : n / 2 = (n - 1) / 2 + 1 := by omega
      have e := wS_succ_bot (h := (n - 1) / 2) (N := n) (by omega)
      rw [← e1] at e
      rw [e]
      have := lagD_spec (D := d + addOf n a' l') hL'.1 hamL hL'.2
      linarith
    · by_cases hodd : n % 2 = 0
      · have h2 : n = 2 := by omega
        subst h2
        have e := wS_succ_bot (h := 0) (N := 2) (by omega)
        simp only [show (2 - 1) / 2 = 0 by rfl, show 2 / 2 = 1 by rfl] at hwadd ⊢
        rw [e, gS_one, sub_zero]
        exact hwadd
      · have e1 : n / 2 = (n - 1) / 2 := by omega
        rw [e1]
        exact hwadd
  refine ⟨⟨by show 2 ≤ n + 1; omega, ?_, ?_, ?_, ?_, ?_, ⟨⟨ha2, hl, hlo⟩, hr⟩, hra', hL', hrl', ?_, ?_, ?_⟩, rfl, ?_⟩
  · simpa using hpsi'
  · simpa using hs'
  · simpa using ht'
  · simpa using hb'
  · simpa using hw'
  -- events
  · dsimp only
    rcases hev with ⟨_, rfl, e⟩ | ⟨_, rfl, rfl, rfl⟩
    · exact e
    · exact hqk
  · dsimp only
    rcases hev with ⟨hqn, rfl, e⟩ | ⟨hqn, rfl, rfl, rfl⟩
    · by_cases hlen : ie + 1 < eventsAll.length
      · left
        have := eventOf_lt (Nat.lt_succ_self ie) hlen
        rw [← hqk, ← e] at this
        simp only at this
        omega
      · right; omega
    · rcases hq with hq | hq
      · left; omega
      · right; exact hq
  · dsimp only
    rcases hev with ⟨hqn, rfl, e⟩ | ⟨hqn, rfl, rfl, rfl⟩
    · intro j hj
      rcases Nat.lt_or_ge j ie with hj' | hj'
      · have := hprev j hj'; omega
      · have : j = ie := by omega
        subst this
        rw [← hqk]
        simp only
        omega
    · intro j hj
      have := hprev j hj
      omega
  -- the checks
  · refine ⟨fun h1 h2 => lt_of_le_of_lt hs' (check16_spec hc16 h1 h2),
      lt_of_le_of_lt ht' (check18_spec hc18), fun h1 => ?_⟩
    exact (primes_le_wS n).trans (hw'.trans (check19_spec hc19 h1 (by omega) han hlo))

theorem walk_succ (f : ℕ) (st : St) :
    walk (f + 1) st = (match step st with
      | none => none
      | some st' => walk f st') := rfl

theorem walk_inv : ∀ (f : ℕ) (st st' : St), Inv st → walk f st = some st' →
    Inv st' ∧ st'.n = st.n + f ∧ ∀ m, st.n ≤ m → m < st.n + f → GoodAt m := by
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
      rcases Nat.lt_or_ge m (st.n + 1) with hm | hm
      · have : m = st.n := by omega
        exact this ▸ hgood
      · exact hgood' m (by omega) (by omega)

/-! ### Chunks -/

theorem ancListEq_eq : ∀ {L L' : List Anc}, ancListEq L L' = true → L = L'
  | [], [], _ => rfl
  | (a, l, lo, r) :: L, (a', l', lo', r') :: L', h => by
    simp only [ancListEq, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, h3, h4, ancListEq_eq h5]
  | [], _ :: _, h => by simp [ancListEq] at h
  | _ :: _, [], h => by simp [ancListEq] at h

theorem stEq_eq {x y : St} (h : stEq x y = true) : x = y := by
  obtain ⟨n, psi, s, t, d, ia, a, l, lo, r, b, ra, ja, aL, loL, bL, rl, ie, q, k⟩ := x
  obtain ⟨n', psi', s', t', d', ia', a', l', lo', r', b', ra', ja', aL', loL', bL', rl', ie', q', k'⟩ := y
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩ := h
  rw [ancListEq_eq h12, ancListEq_eq h17]
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h13 h14 h15 h16 h18 h19 h20
  rfl

theorem walk_of_chunkOK {f : ℕ} {e e' : Ext} (h : chunkOK f e e' = true) :
    walk f (attach e) = some (attach e') := by
  unfold chunkOK at h
  split at h
  · rename_i r hr
    rw [hr, stEq_eq h]
  · exact absurd h (by simp)

theorem attach_n (e : Ext) : (attach e).n = e.1 := by
  obtain ⟨n, psi, s, t, d, ia, ja, ie⟩ := e
  rfl

end RSBounds.HelfgottLow
