/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.RvMFine
import RSBounds.RvMWindow

/-!
# Kernel checkers for a counting window

`pairCheck` walks a located list together with two lists of main-term certificates: for the
zero with global index `i`, the first certificate sits at or below its bracket and shows
`F > base + i + 1 − c` there, the second at or above it and shows `F < base + i + c`.
`window_of_checks` turns these checks, two end certificates and `belowCheck`/`aboveCheck` into
`|base + #{i : γᵢ ≤ T} − F(T)| < c` on the whole window, by `RvMWindow.window_count_error`.
-/

open Set

namespace TernaryGoldbach.RSBounds.RvMCheck
open BacklundLowScalar BacklundLowCount RvMFine RvMWindow

/-- The certificate conditions for each listed zero of the window. -/
def pairCheck (a b : ℚ) (base c : ℕ) : ℕ → List ℕ → List MainCert → List MainCert → Bool
  | _, _, [], [] => true
  | i, m :: ms, cl :: cls, ch :: chs =>
      (decide (a ≤ cl.t) && decide (cl.t * 10 ^ 24 + 10001 ≤ (m : ℚ)) &&
        decide ((m : ℚ) + 10001 ≤ ch.t * 10 ^ 24) && decide (ch.t ≤ b) &&
        decide ((base : ℚ) + i + 1 - c ≤ cl.lo) && decide (ch.hi ≤ (base : ℚ) + i + c)) &&
      pairCheck a b base c (i + 1) ms cls chs
  | _, _, _, _ => false

/-- The listed zeros before the window lie below `a`. -/
def belowCheck (a : ℚ) (K0 : ℕ) (ords : List ℕ) : Bool :=
  (ords.take K0).all (fun m => decide ((m : ℚ) + 10001 ≤ a * 10 ^ 24))

/-- The listed zeros after the window lie above `b`. -/
def aboveCheck (b : ℚ) (K : ℕ) (ords : List ℕ) : Bool :=
  (ords.drop K).all (fun m => decide (b * 10 ^ 24 + 10001 ≤ (m : ℚ)))

theorem pairCheck_sound {a b : ℚ} {base c : ℕ} (ha : 2 * Real.pi ≤ (a : ℝ)) :
    ∀ (cls : List MainCert) (i : ℕ) (ms : List ℕ) (chs : List MainCert),
      pairCheck a b base c i ms cls chs = true →
      (∀ x ∈ cls, FineValid x) → (∀ x ∈ chs, FineValid x) →
      ∀ j (hj : j < cls.length), ∃ hjm : j < ms.length, ∀ γ : ℝ,
        ((ms[j] : ℝ) - 10001) / 10 ^ 24 < γ → γ < ((ms[j] : ℝ) + 10001) / 10 ^ 24 →
        (a : ℝ) ≤ γ ∧ γ ≤ (b : ℝ) ∧
          (base : ℝ) + ((i + j : ℕ) : ℝ) + 1 - c < rosserF γ ∧
          rosserF γ < (base : ℝ) + ((i + j : ℕ) : ℝ) + c
  | [], _, _, _, _, _, _, j, hj => absurd hj (by simp)
  | cl :: cls, i, [], chs, h, _, _, _, _ => by cases chs <;> simp [pairCheck] at h
  | cl :: cls, i, m :: ms, [], h, _, _, _, _ => by simp [pairCheck] at h
  | cl :: cls, i, m :: ms, ch :: chs, h, hvl, hvh, j, hj => by
    simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hrest⟩ := h
    cases j with
    | zero =>
      refine ⟨by simp, fun γ hγl hγu => ?_⟩
      simp only [List.getElem_cons_zero] at hγl hγu
      simp only [Nat.add_zero]
      have hcl := fine_sound (hvl cl (by simp))
      have hch := fine_sound (hvh ch (by simp))
      have h1' : (a : ℝ) ≤ (cl.t : ℝ) := by exact_mod_cast h1
      have h2' : (cl.t : ℝ) * 10 ^ 24 + 10001 ≤ (m : ℝ) := by exact_mod_cast h2
      have h3' : (m : ℝ) + 10001 ≤ (ch.t : ℝ) * 10 ^ 24 := by exact_mod_cast h3
      have h4' : (ch.t : ℝ) ≤ (b : ℝ) := by exact_mod_cast h4
      have h5' : (base : ℝ) + (i : ℝ) + 1 - c ≤ (cl.lo : ℝ) := by exact_mod_cast h5
      have h6' : (ch.hi : ℝ) ≤ (base : ℝ) + (i : ℝ) + c := by exact_mod_cast h6
      have hclγ : (cl.t : ℝ) ≤ γ := by
        have : (cl.t : ℝ) ≤ ((m : ℝ) - 10001) / 10 ^ 24 := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        linarith
      have hγch : γ ≤ (ch.t : ℝ) := by
        have : ((m : ℝ) + 10001) / 10 ^ 24 ≤ (ch.t : ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          linarith
        linarith
      have hp1 : 2 * Real.pi ≤ (cl.t : ℝ) := ha.trans h1'
      have hp2 : 2 * Real.pi ≤ γ := hp1.trans hclγ
      have hF1 := rosserF_monotone hp1 hp2 hclγ
      have hF2 := rosserF_monotone hp2 (hp2.trans hγch) hγch
      refine ⟨h1'.trans hclγ, hγch.trans h4', ?_, ?_⟩
      · linarith [hcl.1]
      · linarith [hch.2]
    | succ j =>
      obtain ⟨hjm, hγ⟩ := pairCheck_sound ha cls (i + 1) ms chs hrest
        (fun x hx => hvl x (List.mem_cons_of_mem _ hx))
        (fun x hx => hvh x (List.mem_cons_of_mem _ hx)) j (by simpa using hj)
      refine ⟨by simpa using hjm, fun γ hγl hγu => ?_⟩
      have e : i + 1 + j = i + (j + 1) := by omega
      have := hγ γ (by simpa using hγl) (by simpa using hγu)
      rw [e] at this
      exact this

theorem two_pi_le_seven : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]

/-- All checks of a window give `|base + #{i : γᵢ ≤ T} − F(T)| < c` on `[a, b]`. -/
theorem window_of_checks {ords : List ℕ} {n A B : ℕ} (hf : ListFacts ords n A B)
    (hc : ListCertified ords A B) {a b : ℚ} {base c K0 K : ℕ} (hK : K0 ≤ K) (hKn : K ≤ n)
    {cls chs : List MainCert} {cA cB : MainCert} (h7 : (7 : ℚ) ≤ a)
    (hlen : cls.length = K - K0)
    (hpair : pairCheck a b base c K0 (ords.drop K0) cls chs = true)
    (hvl : ∀ x ∈ cls, FineValid x) (hvh : ∀ x ∈ chs, FineValid x)
    (hvA : FineValid cA) (hvB : FineValid cB)
    (hbelow : belowCheck a K0 ords = true) (habove : aboveCheck b K ords = true)
    (hA : cA.t = a) (hAlo : (base : ℚ) + K0 - c ≤ cA.lo)
    (hB : cB.t = b) (hBhi : cB.hi ≤ (base : ℚ) + K + c)
    {T : ℝ} (hTa : (a : ℝ) ≤ T) (hTb : T ≤ (b : ℝ)) :
    |(base : ℝ) + (indicesBelow (hf.table hc).ordinate T).card - rosserF T| < c := by
  classical
  set ts := (hf.table hc).ordinate with hts
  have ha7 : (7 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h7
  have ha2 : 2 * Real.pi ≤ (a : ℝ) := two_pi_le_seven.trans ha7
  have hmono : Monotone ts := (hf.table hc).strictMono.monotone
  have hF : MonotoneOn rosserF (Icc (a : ℝ) (b : ℝ)) :=
    rosserF_monotone.mono (fun x hx => ha2.trans hx.1)
  have hlen' : ords.length = n := hf.length
  apply window_count_error hmono hF hK hKn (base := base) (K0 := K0)
  · -- zeros before the window lie below `a`
    intro i hi
    have hmem : hf.ord i ∈ ords.take K0 := by
      apply List.mem_iff_getElem.mpr
      refine ⟨i.val, by have := i.isLt; simp; omega, ?_⟩
      simp [ListFacts.ord]
    have hb := of_decide_eq_true (List.all_eq_true.mp hbelow _ hmem)
    have hord : (hf.ord i : ℝ) + 10001 ≤ (a : ℝ) * 10 ^ 24 := by exact_mod_cast hb
    have : ((hf.ord i : ℝ) + 10001) / 10 ^ 24 ≤ (a : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      exact hord
    exact lt_of_lt_of_le (hf.table_bracket hc i).2 this
  · -- the window
    intro i hi0 hiK
    have hj : i.val - K0 < cls.length := by omega
    obtain ⟨hjm, hγ⟩ := pairCheck_sound ha2 cls K0 (ords.drop K0) chs hpair hvl hvh
      (i.val - K0) hj
    have hget : (ords.drop K0)[i.val - K0]'hjm = hf.ord i := by
      simp only [List.getElem_drop, ListFacts.ord, Nat.add_sub_cancel' hi0]
    have hbr := hf.table_bracket hc i
    rw [← hget] at hbr
    have := hγ (ts i) hbr.1 hbr.2
    have e : K0 + (i.val - K0) = i.val := by omega
    rw [e] at this
    exact this
  · -- zeros after the window lie above `b`
    intro i hi
    have hmem : hf.ord i ∈ ords.drop K := by
      apply List.mem_iff_getElem.mpr
      refine ⟨i.val - K, by have := i.isLt; simp; omega, ?_⟩
      simp only [List.getElem_drop, ListFacts.ord, Nat.add_sub_cancel' hi]
    have hb := of_decide_eq_true (List.all_eq_true.mp habove _ hmem)
    have hord : (b : ℝ) * 10 ^ 24 + 10001 ≤ (hf.ord i : ℝ) := by exact_mod_cast hb
    have : (b : ℝ) ≤ ((hf.ord i : ℝ) - 10001) / 10 ^ 24 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    exact lt_of_le_of_lt this (hf.table_bracket hc i).1
  · exact hTa
  · exact hTb
  · have h := (fine_sound hvA).1
    rw [hA] at h
    have hAlo' : (base : ℝ) + (K0 : ℝ) - (c : ℝ) ≤ (cA.lo : ℝ) := by exact_mod_cast hAlo
    linarith
  · have h := (fine_sound hvB).2
    rw [hB] at h
    have hBhi' : (cB.hi : ℝ) ≤ (base : ℝ) + (K : ℝ) + (c : ℝ) := by exact_mod_cast hBhi
    linarith

end TernaryGoldbach.RSBounds.RvMCheck
