/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.BacklundLowCountGeneric
import RSBounds.RosserCountDefinition

/-!
# Counting zeros in a window `(a, b]` from a located list

`ListCertified ords a b` is the conjunction of the statements `located` and `unique` of a range
file of `Garald1/zeta-zero-locations` (with `a < Im s ≤ b`). Together with three kernel-checkable
facts about the list (`ListFacts`), it gives a `RangeTable`: the exact ordinates of all zeros with
`a < Im ρ ≤ b`, simple and on the critical line, each within `10001 · 10⁻²⁴` of its listed integer.
Then `N(T) = N(a) + #{i : γᵢ ≤ T}` for `a ≤ T ≤ b`.

`window_count_error` turns enclosures of a monotone `F` at the listed ordinates into
`|N(T) − F(T)| < c` for every real `T` in a window, including the jumps.

Nothing here asserts anything about zeta: every result takes `ListCertified` as a hypothesis.
-/

open Complex Set

namespace TernaryGoldbach.RSBounds.RvMWindow
open BacklundCountIdentity BacklundLowCount

/-! ## The window lemma -/

theorem window_count_error {n : ℕ} {ts : Fin n → ℝ} (hm : Monotone ts) {F : ℝ → ℝ}
    {a b T c : ℝ} (hF : MonotoneOn F (Icc a b)) {base K0 K : ℕ} (hK : K0 ≤ K) (hKn : K ≤ n)
    (hbelow : ∀ i : Fin n, i.val < K0 → ts i < a)
    (hwin : ∀ i : Fin n, K0 ≤ i.val → i.val < K → a ≤ ts i ∧ ts i ≤ b ∧
      (base : ℝ) + i.val + 1 - c < F (ts i) ∧ F (ts i) < base + i.val + c)
    (habove : ∀ i : Fin n, K ≤ i.val → b < ts i)
    (hTa : a ≤ T) (hTb : T ≤ b)
    (hlowEnd : (base : ℝ) + K0 - c < F a) (hhighEnd : F b < (base : ℝ) + K + c) :
    |(base : ℝ) + (indicesBelow ts T).card - F T| < c := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, k = (indicesBelow ts T).card := ⟨_, rfl⟩
  rw [← hk]
  have hkn : k ≤ n := hk ▸ card_indicesBelow_le ts T
  have hab : a ≤ b := hTa.trans hTb
  have hTmem : T ∈ Icc a b := ⟨hTa, hTb⟩
  have hK0k : K0 ≤ k := by
    by_contra hlt
    have hlt' : k < K0 := by omega
    have hit : ts ⟨k, by omega⟩ ≤ T := ((hbelow ⟨k, by omega⟩ hlt').le).trans hTa
    have : k < (indicesBelow ts T).card := (le_iff_lt_card hm T ⟨k, by omega⟩).mp hit
    omega
  have hkK : k ≤ K := by
    by_contra hlt
    have hlt' : K < k := by omega
    have hit : ts ⟨K, by omega⟩ ≤ T :=
      (le_iff_lt_card hm T ⟨K, by omega⟩).mpr (show K < (indicesBelow ts T).card by omega)
    have := habove ⟨K, by omega⟩ le_rfl
    linarith
  rw [abs_lt]
  constructor
  · -- `F T < base + k + c`
    suffices h : F T < (base : ℝ) + k + c by linarith
    by_cases hkK' : k = K
    · rw [hkK']
      exact (hF hTmem ⟨hab, le_rfl⟩ hTb).trans_lt hhighEnd
    · have hit : T < ts ⟨k, by omega⟩ := by
        apply lt_of_not_ge
        intro h
        have : k < (indicesBelow ts T).card := (le_iff_lt_card hm T ⟨k, by omega⟩).mp h
        omega
      obtain ⟨hia, hib, -, hhi⟩ := hwin ⟨k, by omega⟩ (show K0 ≤ k by omega)
        (show k < K by omega)
      have hhi' : F (ts ⟨k, by omega⟩) < (base : ℝ) + (k : ℝ) + c := hhi
      exact (hF hTmem ⟨hia, hib⟩ hit.le).trans_lt hhi'
  · -- `base + k - c < F T`
    suffices h : (base : ℝ) + k - c < F T by linarith
    by_cases hk0 : k = K0
    · rw [hk0]
      exact hlowEnd.trans_le (hF ⟨le_rfl, hab⟩ hTmem hTa)
    · have hk1 : 1 ≤ k := by omega
      have hit : ts ⟨k - 1, by omega⟩ ≤ T :=
        (le_iff_lt_card hm T ⟨k - 1, by omega⟩).mpr
          (show k - 1 < (indicesBelow ts T).card by omega)
      obtain ⟨hia, hib, hlo, -⟩ := hwin ⟨k - 1, by omega⟩ (show K0 ≤ k - 1 by omega)
        (show k - 1 < K by omega)
      have hcast : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk1, Nat.cast_one]
      have hlo' : (base : ℝ) + ((k - 1 : ℕ) : ℝ) + 1 - c < F (ts ⟨k - 1, by omega⟩) := hlo
      rw [hcast] at hlo'
      have hmono := hF ⟨hia, hib⟩ hTmem hit
      linarith


/-! ## Range tables and the count -/

/-- All zeros with `a < Im ρ ≤ b`, in increasing order, simple and on the critical line. -/
structure RangeTable (n : ℕ) (a b : ℝ) where
  ordinate : Fin n → ℝ
  strictMono : StrictMono ordinate
  above : ∀ i, a < ordinate i
  le_top : ∀ i, ordinate i ≤ b
  zero : ∀ i, riemannZeta (1 / 2 + ordinate i * I) = 0
  simple : ∀ i, analyticOrderAt riemannZeta (1 / 2 + ordinate i * I) = 1
  complete : ∀ ρ : ℂ, riemannZeta ρ = 0 → a < ρ.im → ρ.im ≤ b → ∃ i, ρ = 1 / 2 + ordinate i * I

namespace RangeTable

variable {n : ℕ} {a b : ℝ}

theorem point_injective (t : RangeTable n a b) :
    Function.Injective (fun i => (1 / 2 : ℂ) + t.ordinate i * I) := by
  intro i j hij
  apply t.strictMono.injective
  simpa using congrArg Complex.im hij

/-- The zeros counted by `N(T)` above height `a` are the listed ones below `T`. -/
theorem image_eq (t : RangeTable n a b) (ha : 0 ≤ a) {T : ℝ} (hT : 0 < T) (hTb : T ≤ b) :
    (indicesBelow t.ordinate T).image (fun i => (1 / 2 : ℂ) + t.ordinate i * I) =
      (closedPositiveZeros T).filter (fun ρ => ¬ ρ.im ≤ a) := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, mem_indicesBelow,
    mem_closedPositiveZeros_iff hT]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have h0 := t.above i
    refine ⟨⟨t.zero i, by simp; linarith, by simpa using hi⟩, by simp; linarith⟩
  · rintro ⟨⟨hz, h0, h1⟩, h2⟩
    obtain ⟨i, rfl⟩ := t.complete z hz (lt_of_not_ge h2) (h1.trans hTb)
    exact ⟨i, by simpa using h1, rfl⟩

theorem sum_image_eq (t : RangeTable n a b) (ha : 0 ≤ a) {T : ℝ} (hT : 0 < T) (hTb : T ≤ b) :
    (∑ ρ ∈ (closedPositiveZeros T).filter (fun ρ => ¬ ρ.im ≤ a),
      (analyticOrderAt riemannZeta ρ).toNat) = (indicesBelow t.ordinate T).card := by
  classical
  rw [← t.image_eq ha hT hTb, Finset.sum_image (fun i _ j _ hij => t.point_injective hij)]
  have hone : ∀ i, (analyticOrderAt riemannZeta ((1 / 2 : ℂ) + t.ordinate i * I)).toNat = 1 := by
    intro i
    rw [t.simple i, ENat.toNat_one]
  simp only [hone, Finset.sum_const, smul_eq_mul, mul_one]

/-- For a table starting at height `0`: `N(T) = #{i : γᵢ ≤ T}`. -/
theorem N_le_eq_card (t : RangeTable n a b) (ha : a = 0) {T : ℝ} (hT : 0 < T) (hTb : T ≤ b) :
    N_le T = (indicesBelow t.ordinate T).card := by
  classical
  subst ha
  rw [← t.sum_image_eq le_rfl hT hTb]
  unfold N_le
  congr 1
  ext ρ
  simp only [Finset.mem_filter, mem_closedPositiveZeros_iff hT]
  constructor
  · rintro ⟨hz, h0, h1⟩
    exact ⟨⟨hz, h0, h1⟩, not_le.mpr h0⟩
  · rintro ⟨h, -⟩
    exact h

/-- For a table above a positive height `a`: `N(T) = N(a) + #{i : γᵢ ≤ T}`. -/
theorem N_le_eq_add (t : RangeTable n a b) (ha : 0 < a) {T : ℝ} (hTa : a ≤ T) (hTb : T ≤ b) :
    N_le T = N_le a + (indicesBelow t.ordinate T).card := by
  classical
  have hT : 0 < T := ha.trans_le hTa
  rw [← t.sum_image_eq ha.le hT hTb]
  unfold N_le
  rw [← Finset.sum_filter_add_sum_filter_not (closedPositiveZeros T) (fun ρ => ρ.im ≤ a)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext ρ
  simp only [Finset.mem_filter, mem_closedPositiveZeros_iff hT, mem_closedPositiveZeros_iff ha]
  constructor
  · rintro ⟨⟨hz, h0, -⟩, h2⟩
    exact ⟨hz, h0, h2⟩
  · rintro ⟨hz, h0, h2⟩
    exact ⟨⟨hz, h0, h2.trans hTa⟩, h2⟩

end RangeTable

/-! ## From a located list to a range table -/

/-- The statements `located` and `unique` of a range file, for `a < Im s ≤ b`. -/
def ListCertified (ords : List ℕ) (a b : ℕ) : Prop :=
  (∀ s : ℂ, riemannZeta s = 0 → (a : ℝ) < s.im → s.im ≤ (b : ℝ) →
      s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
        ∃ m ∈ ords, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    (∀ m ∈ ords, ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20)

/-- Every entry `m` satisfies `a·10²⁴ + 10001 ≤ m` and `m + 10001 ≤ b·10²⁴`. -/
def rangeCheck (a b : ℕ) : List ℕ → Bool
  | [] => true
  | m :: l => (Nat.ble (Nat.add (Nat.mul a (Nat.pow 10 24)) 10001) m &&
      Nat.ble (Nat.add m 10001) (Nat.mul b (Nat.pow 10 24))) && rangeCheck a b l

/-- Consecutive entries differ by at least `20002`. -/
def gapCheck : List ℕ → Bool
  | a :: b :: l => Nat.ble (Nat.add a 20002) b && gapCheck (b :: l)
  | _ => true

theorem rangeCheck_sound (a b : ℕ) : ∀ l : List ℕ, rangeCheck a b l = true →
    ∀ m ∈ l, a * 10 ^ 24 + 10001 ≤ m ∧ m + 10001 ≤ b * 10 ^ 24
  | [], _, m, hm => by simp at hm
  | x :: l, hc, m, hm => by
    simp only [rangeCheck, Bool.and_eq_true, Nat.ble_eq, Nat.pow_eq, Nat.add_eq,
      Nat.mul_eq] at hc
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hc.1
    · exact rangeCheck_sound a b l hc.2 m hm

theorem gapCheck_sound : ∀ l : List ℕ, gapCheck l = true →
    ∀ (i : ℕ) (h : i + 1 < l.length), l[i] + 20002 ≤ l[i + 1]
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | a :: b :: l, hc, i, h => by
    simp only [gapCheck, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at hc
    cases i with
    | zero => simpa using hc.1
    | succ i =>
      have := gapCheck_sound (b :: l) hc.2 i (by simp only [List.length_cons] at h ⊢; omega)
      simpa using this

/-- Kernel-checkable facts about the list alone. -/
structure ListFacts (ords : List ℕ) (n a b : ℕ) : Prop where
  length : ords.length = n
  range : rangeCheck a b ords = true
  gap : gapCheck ords = true

namespace ListFacts

variable {ords : List ℕ} {n a b : ℕ}

/-- The `i`-th listed integer. -/
def ord (hf : ListFacts ords n a b) (i : Fin n) : ℕ :=
  ords[i.1]'(Nat.lt_of_lt_of_eq i.2 hf.length.symm)

theorem ord_mem (hf : ListFacts ords n a b) (i : Fin n) : hf.ord i ∈ ords := List.getElem_mem _

theorem ord_real_range (hf : ListFacts ords n a b) (i : Fin n) :
    (a : ℝ) * 10 ^ 24 + 10001 ≤ (hf.ord i : ℝ) ∧ (hf.ord i : ℝ) + 10001 ≤ (b : ℝ) * 10 ^ 24 := by
  obtain ⟨h1, h2⟩ := rangeCheck_sound a b ords hf.range (hf.ord i) (hf.ord_mem i)
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem ord_gap (hf : ListFacts ords n a b) (i : ℕ) (h : i + 1 < n) :
    hf.ord ⟨i, by omega⟩ + 20002 ≤ hf.ord ⟨i + 1, h⟩ :=
  gapCheck_sound ords hf.gap i (by rw [hf.length]; exact h)

variable (hf : ListFacts ords n a b) (hc : ListCertified ords a b)
include hf hc

theorem exists_unique_zero (i : Fin n) :
    ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (hf.ord i : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 :=
  hc.2 (hf.ord i) (hf.ord_mem i)

/-- The zero attached to the `i`-th listed integer by `unique`. -/
noncomputable def zero (i : Fin n) : ℂ := (exists_unique_zero hf hc i).exists.choose

theorem zero_spec (i : Fin n) :
    riemannZeta (zero hf hc i) = 0 ∧
      |(zero hf hc i).im - (hf.ord i : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 :=
  (exists_unique_zero hf hc i).exists.choose_spec

/-- The bracket used by the main-term certificates. -/
theorem im_bounds (i : Fin n) :
    ((hf.ord i : ℝ) - 10001) / 10 ^ 24 < (zero hf hc i).im ∧
      (zero hf hc i).im < ((hf.ord i : ℝ) + 10001) / 10 ^ 24 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (zero_spec hf hc i).2
  have e1 : ((hf.ord i : ℝ) - 10001) / 10 ^ 24 = (hf.ord i : ℝ) / 10 ^ 24 - 10001 / 10 ^ 24 := by
    ring
  have e2 : ((hf.ord i : ℝ) + 10001) / 10 ^ 24 = (hf.ord i : ℝ) / 10 ^ 24 + 10001 / 10 ^ 24 := by
    ring
  have hc' : (1 : ℝ) / 10 ^ 20 < 10001 / 10 ^ 24 := by norm_num
  constructor <;> linarith

theorem zero_in_range (i : Fin n) : (a : ℝ) < (zero hf hc i).im ∧ (zero hf hc i).im ≤ b := by
  obtain ⟨hlo, hhi⟩ := im_bounds hf hc i
  obtain ⟨h1, h2⟩ := hf.ord_real_range i
  constructor
  · have : (a : ℝ) ≤ ((hf.ord i : ℝ) - 10001) / 10 ^ 24 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  · have : ((hf.ord i : ℝ) + 10001) / 10 ^ 24 ≤ b := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

theorem zero_re (i : Fin n) : (zero hf hc i).re = 1 / 2 :=
  (hc.1 _ (zero_spec hf hc i).1 (zero_in_range hf hc i).1 (zero_in_range hf hc i).2).1

theorem zero_simple (i : Fin n) : analyticOrderAt riemannZeta (zero hf hc i) = 1 :=
  (hc.1 _ (zero_spec hf hc i).1 (zero_in_range hf hc i).1 (zero_in_range hf hc i).2).2.1

theorem zero_eq (i : Fin n) : zero hf hc i = 1 / 2 + ((zero hf hc i).im : ℂ) * I := by
  apply Complex.ext <;> simp [zero_re hf hc i]

theorem ordinate_strictMono : StrictMono (fun i => (zero hf hc i).im) := by
  rcases n with _ | m
  · intro i
    exact i.elim0
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hg : (hf.ord i.castSucc : ℝ) + 20002 ≤ (hf.ord i.succ : ℝ) := by
    have := hf.ord_gap i.1 (by have := i.isLt; omega)
    exact_mod_cast this
  have h1 := (im_bounds hf hc i.castSucc).2
  have h2 := (im_bounds hf hc i.succ).1
  have hmid : ((hf.ord i.castSucc : ℝ) + 10001) / 10 ^ 24 ≤
      ((hf.ord i.succ : ℝ) - 10001) / 10 ^ 24 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  show (zero hf hc i.castSucc).im < (zero hf hc i.succ).im
  linarith

theorem complete_aux (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : (a : ℝ) < ρ.im)
    (h1 : ρ.im ≤ b) : ∃ i : Fin n, ρ = 1 / 2 + ((zero hf hc i).im : ℂ) * I := by
  obtain ⟨-, -, m, hm, hwin⟩ := hc.1 ρ hz h0 h1
  obtain ⟨k, hk, hkm⟩ := List.getElem_of_mem hm
  let i : Fin n := ⟨k, Nat.lt_of_lt_of_eq hk hf.length⟩
  have hord : hf.ord i = m := hkm
  refine ⟨i, ?_⟩
  have hρ : ρ = zero hf hc i := by
    apply (exists_unique_zero hf hc i).unique _ (zero_spec hf hc i)
    rw [hord]
    exact ⟨hz, hwin⟩
  rw [hρ]
  exact zero_eq hf hc i

/-- The range table built from the list. -/
noncomputable def table : RangeTable n a b where
  ordinate i := (zero hf hc i).im
  strictMono := ordinate_strictMono hf hc
  above i := (zero_in_range hf hc i).1
  le_top i := (zero_in_range hf hc i).2
  zero i := by
    rw [← zero_eq hf hc i]
    exact (zero_spec hf hc i).1
  simple i := by
    rw [← zero_eq hf hc i]
    exact zero_simple hf hc i
  complete ρ hz h0 h1 := complete_aux hf hc ρ hz h0 h1

theorem table_bracket (i : Fin n) :
    ((hf.ord i : ℝ) - 10001) / 10 ^ 24 < (table hf hc).ordinate i ∧
      (table hf hc).ordinate i < ((hf.ord i : ℝ) + 10001) / 10 ^ 24 :=
  im_bounds hf hc i

end ListFacts

end TernaryGoldbach.RSBounds.RvMWindow
