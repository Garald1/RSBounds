/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.RvMSmall
import RSBounds.RvMData0
import RSBounds.RvMData1
import RSBounds.RvMData2
import RSBounds.RvMData3
import RSBounds.RvMData4
import RSBounds.RvMData5
import RSBounds.Rosser1941

/-!
# `|N(t) − F(t)| ≤ (1/5) log t + 2` for `t ≥ 1`

IEANTN's `ZeroCount.v1.rvm_error_bound` (whose docstring attributes it to Chirre–Helfgott,
Lemma B.1), for the project's count `Rosser1941.positiveZeroCount` (zeros with
`0 < Im ρ ≤ t`, with multiplicity) and `F(t) = (t/2π) log(t/2π) − t/2π + 7/8`.

* On `[1, 280]`: `RvMSmall.rvm_error_small` gives `|N − F| < 1`.
* On `[280, 6000]`: the certificates of `RvMData0` … `RvMData5` give `|N − F| < 3`, and
  `(1/5) log t + 2 ≥ 3` there.
* On `[6000, ∞)`: Rosser's `0.137 log t + 0.443 log log t + 1.588` (`Rosser1941.zero_count_bounds`,
  unconditional) is at most `(1/5) log t + 2`. Below `6000` it is not on all of
  `(300.4, 5165.6)`, which is why the zeros are needed there.

Conditional on `Head1000.Certified` and on `located` and `unique` of the five range files
`Zeros1000to2000` … `Zeros5000to6000` of `Garald1/zeta-zero-locations`.
-/

open Real

namespace TernaryGoldbach.RSBounds.RvMBound
open BacklundLowScalar BacklundLowCount BacklundCountIdentity RvMFine RvMWindow RvMCheck RvMSmall

/-- `located` and `unique` of `challenge/Zeros1000to2000.lean`, verbatim, as one proposition. -/
def Certified1 : Prop :=
  (∀ s ∈ Zeros1000to2000.zerosBetween 1000 2000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros1000to2000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    ∀ m ∈ Zeros1000to2000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

theorem listCertified1 (h : Certified1) : ListCertified Zeros1000to2000.ordinates 1000 2000 :=
  ⟨fun s hz h0 h1 => h.1 s ⟨hz, by simpa using h0, by simpa using h1⟩, h.2⟩

/-- `located` and `unique` of `challenge/Zeros2000to3000.lean`, verbatim, as one proposition. -/
def Certified2 : Prop :=
  (∀ s ∈ Zeros2000to3000.zerosBetween 2000 3000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros2000to3000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    ∀ m ∈ Zeros2000to3000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

theorem listCertified2 (h : Certified2) : ListCertified Zeros2000to3000.ordinates 2000 3000 :=
  ⟨fun s hz h0 h1 => h.1 s ⟨hz, by simpa using h0, by simpa using h1⟩, h.2⟩

/-- `located` and `unique` of `challenge/Zeros3000to4000.lean`, verbatim, as one proposition. -/
def Certified3 : Prop :=
  (∀ s ∈ Zeros3000to4000.zerosBetween 3000 4000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros3000to4000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    ∀ m ∈ Zeros3000to4000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

theorem listCertified3 (h : Certified3) : ListCertified Zeros3000to4000.ordinates 3000 4000 :=
  ⟨fun s hz h0 h1 => h.1 s ⟨hz, by simpa using h0, by simpa using h1⟩, h.2⟩

/-- `located` and `unique` of `challenge/Zeros4000to5000.lean`, verbatim, as one proposition. -/
def Certified4 : Prop :=
  (∀ s ∈ Zeros4000to5000.zerosBetween 4000 5000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros4000to5000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    ∀ m ∈ Zeros4000to5000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

theorem listCertified4 (h : Certified4) : ListCertified Zeros4000to5000.ordinates 4000 5000 :=
  ⟨fun s hz h0 h1 => h.1 s ⟨hz, by simpa using h0, by simpa using h1⟩, h.2⟩

/-- `located` and `unique` of `challenge/Zeros5000to6000.lean`, verbatim, as one proposition. -/
def Certified5 : Prop :=
  (∀ s ∈ Zeros5000to6000.zerosBetween 5000 6000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros5000to6000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    ∀ m ∈ Zeros5000to6000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

theorem listCertified5 (h : Certified5) : ListCertified Zeros5000to6000.ordinates 5000 6000 :=
  ⟨fun s hz h0 h1 => h.1 s ⟨hz, by simpa using h0, by simpa using h1⟩, h.2⟩

/-! ## The windows -/

theorem window3 {ords : List ℕ} {n A B : ℕ} (hf : ListFacts ords n A B)
    (hc : ListCertified ords A B) {a b : ℚ} {base K0 K : ℕ} (hK : K0 ≤ K) (hKn : K ≤ n)
    {cls : List MainCert} {cA cB : MainCert} (h7 : (7 : ℚ) ≤ a) (hlen : cls.length = K - K0)
    (hvalid : (cls ++ [cA, cB]).all (fun x => decide (FineValid x)) = true)
    (hpair : pairCheck a b base 3 K0 (ords.drop K0) cls (cls.tail ++ [cB]) = true)
    (hbelow : belowCheck a K0 ords = true) (habove : aboveCheck b K ords = true)
    (hends : cA.t = a ∧ ((base : ℕ) : ℚ) + (K0 : ℕ) - (3 : ℕ) ≤ cA.lo ∧ cB.t = b ∧
      cB.hi ≤ ((base : ℕ) : ℚ) + (K : ℕ) + (3 : ℕ))
    {T : ℝ} (hTa : (a : ℝ) ≤ T) (hTb : T ≤ (b : ℝ)) :
    |(base : ℝ) + (indicesBelow (hf.table hc).ordinate T).card - rosserF T| < 3 := by
  have hv := all_valid hvalid
  have hcls : ∀ x ∈ cls, FineValid x := fun x hx => hv x (List.mem_append_left _ hx)
  have hchs : ∀ x ∈ cls.tail ++ [cB], FineValid x := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hcls x (List.mem_of_mem_tail h)
    · exact hv x (List.mem_append_right _ (by simp at h; simp [h]))
  have := window_of_checks hf hc hK hKn (c := 3) h7 hlen hpair hcls hchs
    (hv _ (by simp)) (hv _ (by simp)) hbelow habove hends.1 hends.2.1 hends.2.2.1 hends.2.2.2
    hTa hTb
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num] at this
  exact this

theorem card_all {n : ℕ} {a b : ℝ} (t : RangeTable n a b) {T : ℝ} (hT : b ≤ T) :
    (indicesBelow t.ordinate T).card = n := by
  classical
  have : indicesBelow t.ordinate T = Finset.univ := by
    ext i
    simp [(t.le_top i).trans hT]
  rw [this, Finset.card_univ, Fintype.card_fin]

noncomputable def table1 (h : Certified1) := RvMData1.facts.table (listCertified1 h)
noncomputable def table2 (h : Certified2) := RvMData2.facts.table (listCertified2 h)
noncomputable def table3 (h : Certified3) := RvMData3.facts.table (listCertified3 h)
noncomputable def table4 (h : Certified4) := RvMData4.facts.table (listCertified4 h)
noncomputable def table5 (h : Certified5) := RvMData5.facts.table (listCertified5 h)

theorem w0 (h : Head1000.Certified) {T : ℝ} (h1 : 280 ≤ T) (h2 : T ≤ 1000) :
    |((indicesBelow (table0 h).ordinate T).card : ℝ) - rosserF T| < 3 := by
  have key : ∀ x : ℝ, |((0 : ℕ) : ℝ) + x - rosserF T| < 3 → |x - rosserF T| < 3 :=
    fun x hx => by simpa using hx
  have := window3 RvMData0Small.facts (certified0 h) (a := 280) (b := 1000) (base := 0)
    (K0 := 126) (K := 649) (by norm_num) (by norm_num) (by norm_num) RvMData0.len
    RvMData0.valid RvMData0.pair RvMData0.below RvMData0.above RvMData0.ends
    (T := T) (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact key _ this

theorem w1 (h : Certified1) {T : ℝ} (h1 : 1000 ≤ T) (h2 : T ≤ 2000) :
    |((649 : ℕ) : ℝ) + ((indicesBelow (table1 h).ordinate T).card : ℝ) - rosserF T| < 3 := by
  have := window3 RvMData1.facts (listCertified1 h) (a := 1000) (b := 2000) (base := 649)
    (K0 := 0) (K := 868) (by norm_num) (by norm_num) (by norm_num) RvMData1.len
    RvMData1.valid RvMData1.pair RvMData1.below RvMData1.above RvMData1.ends
    (T := T) (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact this

theorem w2 (h : Certified2) {T : ℝ} (h1 : 2000 ≤ T) (h2 : T ≤ 3000) :
    |((1517 : ℕ) : ℝ) + ((indicesBelow (table2 h).ordinate T).card : ℝ) - rosserF T| < 3 := by
  have := window3 RvMData2.facts (listCertified2 h) (a := 2000) (b := 3000) (base := 1517)
    (K0 := 0) (K := 952) (by norm_num) (by norm_num) (by norm_num) RvMData2.len
    RvMData2.valid RvMData2.pair RvMData2.below RvMData2.above RvMData2.ends
    (T := T) (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact this

theorem w3 (h : Certified3) {T : ℝ} (h1 : 3000 ≤ T) (h2 : T ≤ 4000) :
    |((2469 : ℕ) : ℝ) + ((indicesBelow (table3 h).ordinate T).card : ℝ) - rosserF T| < 3 := by
  have := window3 RvMData3.facts (listCertified3 h) (a := 3000) (b := 4000) (base := 2469)
    (K0 := 0) (K := 1005) (by norm_num) (by norm_num) (by norm_num) RvMData3.len
    RvMData3.valid RvMData3.pair RvMData3.below RvMData3.above RvMData3.ends
    (T := T) (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact this

theorem w4 (h : Certified4) {T : ℝ} (h1 : 4000 ≤ T) (h2 : T ≤ 5000) :
    |((3474 : ℕ) : ℝ) + ((indicesBelow (table4 h).ordinate T).card : ℝ) - rosserF T| < 3 := by
  have := window3 RvMData4.facts (listCertified4 h) (a := 4000) (b := 5000) (base := 3474)
    (K0 := 0) (K := 1046) (by norm_num) (by norm_num) (by norm_num) RvMData4.len
    RvMData4.valid RvMData4.pair RvMData4.below RvMData4.above RvMData4.ends
    (T := T) (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact this

theorem w5 (h : Certified5) {T : ℝ} (h1 : 5000 ≤ T) (h2 : T ≤ 6000) :
    |((4520 : ℕ) : ℝ) + ((indicesBelow (table5 h).ordinate T).card : ℝ) - rosserF T| < 3 := by
  have := window3 RvMData5.facts (listCertified5 h) (a := 5000) (b := 6000) (base := 4520)
    (K0 := 0) (K := 1078) (by norm_num) (by norm_num) (by norm_num) RvMData5.len
    RvMData5.valid RvMData5.pair RvMData5.below RvMData5.above RvMData5.ends
    (T := T) (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact this

/-! ## The count at the window ends -/

theorem N_le_eq0 (h : Head1000.Certified) {T : ℝ} (hT : 0 < T) (h1 : T ≤ 1000) :
    N_le T = (indicesBelow (table0 h).ordinate T).card :=
  RangeTable.N_le_eq_card (table0 h) Nat.cast_zero hT (by norm_num; linarith)

theorem N_le_1000 (h : Head1000.Certified) : N_le 1000 = 649 := by
  rw [N_le_eq0 h (by norm_num) le_rfl]
  exact card_all (table0 h) (by norm_num)

theorem N_le_eq1 (h0 : Head1000.Certified) (h1 : Certified1) {T : ℝ} (hlo : 1000 ≤ T) (hhi : T ≤ 2000) :
    N_le T = 649 + (indicesBelow (table1 h1).ordinate T).card := by
  rw [RangeTable.N_le_eq_add (table1 h1) (by norm_num) (by norm_num; linarith)
    (by norm_num; linarith)]
  have e : N_le ((1000 : ℕ) : ℝ) = 649 := by
    rw [Nat.cast_ofNat]
    exact N_le_1000 h0
  rw [e]

theorem N_le_2000 (h0 : Head1000.Certified) (h1 : Certified1) : N_le 2000 = 1517 := by
  rw [N_le_eq1 h0 h1 (by norm_num) le_rfl]
  rw [card_all (table1 h1) (by norm_num)]

theorem N_le_eq2 (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2) {T : ℝ} (hlo : 2000 ≤ T) (hhi : T ≤ 3000) :
    N_le T = 1517 + (indicesBelow (table2 h2).ordinate T).card := by
  rw [RangeTable.N_le_eq_add (table2 h2) (by norm_num) (by norm_num; linarith)
    (by norm_num; linarith)]
  have e : N_le ((2000 : ℕ) : ℝ) = 1517 := by
    rw [Nat.cast_ofNat]
    exact N_le_2000 h0 h1
  rw [e]

theorem N_le_3000 (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2) : N_le 3000 = 2469 := by
  rw [N_le_eq2 h0 h1 h2 (by norm_num) le_rfl]
  rw [card_all (table2 h2) (by norm_num)]

theorem N_le_eq3 (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2) (h3 : Certified3) {T : ℝ} (hlo : 3000 ≤ T) (hhi : T ≤ 4000) :
    N_le T = 2469 + (indicesBelow (table3 h3).ordinate T).card := by
  rw [RangeTable.N_le_eq_add (table3 h3) (by norm_num) (by norm_num; linarith)
    (by norm_num; linarith)]
  have e : N_le ((3000 : ℕ) : ℝ) = 2469 := by
    rw [Nat.cast_ofNat]
    exact N_le_3000 h0 h1 h2
  rw [e]

theorem N_le_4000 (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2) (h3 : Certified3) : N_le 4000 = 3474 := by
  rw [N_le_eq3 h0 h1 h2 h3 (by norm_num) le_rfl]
  rw [card_all (table3 h3) (by norm_num)]

theorem N_le_eq4 (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2) (h3 : Certified3) (h4 : Certified4) {T : ℝ} (hlo : 4000 ≤ T) (hhi : T ≤ 5000) :
    N_le T = 3474 + (indicesBelow (table4 h4).ordinate T).card := by
  rw [RangeTable.N_le_eq_add (table4 h4) (by norm_num) (by norm_num; linarith)
    (by norm_num; linarith)]
  have e : N_le ((4000 : ℕ) : ℝ) = 3474 := by
    rw [Nat.cast_ofNat]
    exact N_le_4000 h0 h1 h2 h3
  rw [e]

theorem N_le_5000 (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2) (h3 : Certified3) (h4 : Certified4) : N_le 5000 = 4520 := by
  rw [N_le_eq4 h0 h1 h2 h3 h4 (by norm_num) le_rfl]
  rw [card_all (table4 h4) (by norm_num)]

theorem N_le_eq5 (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2) (h3 : Certified3) (h4 : Certified4) (h5 : Certified5) {T : ℝ} (hlo : 5000 ≤ T) (hhi : T ≤ 6000) :
    N_le T = 4520 + (indicesBelow (table5 h5).ordinate T).card := by
  rw [RangeTable.N_le_eq_add (table5 h5) (by norm_num) (by norm_num; linarith)
    (by norm_num; linarith)]
  have e : N_le ((5000 : ℕ) : ℝ) = 4520 := by
    rw [Nat.cast_ofNat]
    exact N_le_5000 h0 h1 h2 h3 h4
  rw [e]

theorem N_le_6000 (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2) (h3 : Certified3) (h4 : Certified4) (h5 : Certified5) : N_le 6000 = 5598 := by
  rw [N_le_eq5 h0 h1 h2 h3 h4 h5 (by norm_num) le_rfl]
  rw [card_all (table5 h5) (by norm_num)]

/-! ## Assembly -/

/-- `|N(T) − F(T)| < 3` on `[280, 6000]`. -/
theorem count_window (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2)
    (h3 : Certified3) (h4 : Certified4) (h5 : Certified5) {T : ℝ} (hlo : 280 ≤ T)
    (hhi : T ≤ 6000) : |(N_le T : ℝ) - rosserF T| < 3 := by
  have hT : 0 < T := by linarith
  by_cases c1 : T ≤ 1000
  · rw [N_le_eq0 h0 hT c1]
    exact w0 h0 hlo c1
  by_cases c2 : T ≤ 2000
  · rw [N_le_eq1 h0 h1 (by linarith) c2]
    rw [Nat.cast_add]
    exact w1 h1 (by linarith) c2
  by_cases c3 : T ≤ 3000
  · rw [N_le_eq2 h0 h1 h2 (by linarith) c3]
    rw [Nat.cast_add]
    exact w2 h2 (by linarith) c3
  by_cases c4 : T ≤ 4000
  · rw [N_le_eq3 h0 h1 h2 h3 (by linarith) c4]
    rw [Nat.cast_add]
    exact w3 h3 (by linarith) c4
  by_cases c5 : T ≤ 5000
  · rw [N_le_eq4 h0 h1 h2 h3 h4 (by linarith) c5]
    rw [Nat.cast_add]
    exact w4 h4 (by linarith) c5
  · rw [N_le_eq5 h0 h1 h2 h3 h4 h5 (by linarith) hhi]
    rw [Nat.cast_add]
    exact w5 h5 (by linarith) hhi

theorem log_lower_of_cert {c : LogCert} (hc : c.Valid) {l : ℚ} (hl : l ≤ c.lower) {x : ℝ}
    (hx : (c.ratio : ℝ) ≤ x) : (l : ℝ) ≤ Real.log x := by
  have hr : (0 : ℝ) < (c.ratio : ℝ) := by
    unfold LogCert.ratio
    push_cast
    positivity
  calc (l : ℝ) ≤ (c.lower : ℝ) := by exact_mod_cast hl
    _ ≤ Real.log (c.ratio : ℝ) := (LogCert.log_bounds hc).1
    _ ≤ Real.log x := Real.log_le_log hr hx

theorem log_ge_five {t : ℝ} (ht : 280 ≤ t) : 5 ≤ Real.log t := by
  have h := log_lower_of_cert (c := ⟨8, 32, 3⟩) (by decide) (l := 5) (by decide +kernel)
    (x := t) (by
      have e : LogCert.ratio ⟨8, 32, 3⟩ = 280 := by decide +kernel
      rw [e]
      exact_mod_cast ht)
  exact_mod_cast h

/-- Rosser's envelope is below `(1/5) log t + 2` from `6000` on. -/
theorem rosser_le_bound {t : ℝ} (ht : 6000 ≤ t) :
    0.137 * Real.log t + 0.443 * Real.log (Real.log t) + 1.588 ≤ 1 / 5 * Real.log t + 2 := by
  set L := Real.log t with hL
  have hL0 : (869 / 100 : ℝ) ≤ L := by
    have h := log_lower_of_cert (c := ⟨12, 256, 119⟩) (by decide) (l := 869 / 100)
      (by decide +kernel) (x := t) (by
        have e : LogCert.ratio ⟨12, 256, 119⟩ = 6000 := by decide +kernel
        rw [e]
        exact_mod_cast ht)
    have e : ((869 / 100 : ℚ) : ℝ) = 869 / 100 := by norm_num
    rw [e] at h
    exact h
  have hLpos : 0 < L := by linarith
  have hc : LogCert.Valid ⟨3, 800, 69⟩ := by decide
  have hu : (LogCert.upper ⟨3, 800, 69⟩ : ℚ) ≤ 216218 / 100000 := by decide +kernel
  have hr : LogCert.ratio ⟨3, 800, 69⟩ = 869 / 100 := by decide +kernel
  have hlog869 : Real.log (869 / 100) ≤ 216218 / 100000 := by
    have h1 := (LogCert.log_bounds hc).2
    rw [hr] at h1
    have h2 : ((LogCert.upper ⟨3, 800, 69⟩ : ℚ) : ℝ) ≤ ((216218 / 100000 : ℚ) : ℝ) := by
      exact_mod_cast hu
    have e1 : (((869 / 100 : ℚ)) : ℝ) = 869 / 100 := by norm_num
    have e2 : (((216218 / 100000 : ℚ)) : ℝ) = 216218 / 100000 := by norm_num
    rw [e1] at h1
    rw [e2] at h2
    linarith
  have htan : Real.log L ≤ Real.log (869 / 100) + (L / (869 / 100) - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < L / (869 / 100) by positivity)
    rw [Real.log_div hLpos.ne' (by norm_num)] at h
    linarith
  have : L / (869 / 100) = 100 / 869 * L := by ring
  rw [this] at htan
  nlinarith

/-- **`ZeroCount.v1.rvm_error_bound`**, for the project's count: `|N(t) − F(t)| ≤ (1/5) log t + 2`
for `t ≥ 1`, given the statements of `Zeros0to1000` … `Zeros5000to6000`. -/
theorem rvm_error_bound (h0 : Head1000.Certified) (h1 : Certified1) (h2 : Certified2)
    (h3 : Certified3) (h4 : Certified4) (h5 : Certified5) (t : ℝ) (ht : 1 ≤ t) :
    |Rosser1941.positiveZeroCount t -
      (t / (2 * π) * log (t / (2 * π)) - t / (2 * π) + 7 / 8)| ≤ 1 / 5 * log t + 2 := by
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  by_cases h280 : t ≤ 280
  · have := rvm_error_small h0 t (by linarith) h280
    linarith
  have h280' : 280 ≤ t := (not_le.mp h280).le
  have ht0 : 0 < t := by linarith
  have h5' := log_ge_five h280'
  by_cases h6000 : t ≤ 6000
  · rw [Rosser1941.positiveZeroCount_eq ht0]
    have := count_window h0 h1 h2 h3 h4 h5 h280' h6000
    unfold rosserF at this
    linarith
  · have hR := Rosser1941.zero_count_bounds t (by linarith)
    have hb := rosser_le_bound (not_le.mp h6000).le
    linarith

end TernaryGoldbach.RSBounds.RvMBound
