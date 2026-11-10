/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.RvMData0Small
import RSBounds.Head1000Table

/-!
# `|N(t) − F(t)| < 1` for `0 < t ≤ 280`

`F(t) = (t/2π) log(t/2π) − t/2π + 7/8` and `N(t)` counts the zeros with `0 < Im ρ ≤ t`, with
multiplicity (`Rosser1941.positiveZeroCount`). This is IEANTN's `ZeroCount.v1.rvm_error_small`
(whose docstring attributes it to Chirre–Helfgott, Lemma B.1).

Up to `100` it is the project's unconditional `Rosser1941.zero_count_error_lt_one_to_100`. On
`[100, 280]` it is conditional on `Head1000.Certified`, the statements `located`, `unique` and
`count` of `Zeros0to1000` (`Garald1/zeta-zero-locations`), and is checked from the certificates
of `RvMData0Small`. The tightest point is the zero at `t = 169.912`, where `N − F` is `0.99786`.
-/

open Real

namespace TernaryGoldbach.RSBounds.RvMSmall
open BacklundLowScalar BacklundLowCount BacklundCountIdentity RvMFine RvMWindow RvMCheck

/-- `Head1000.Certified` in the form used by `RvMWindow`. -/
theorem certified0 (h : Head1000.Certified) : ListCertified Zeros0to1000.ordinates 0 1000 :=
  ⟨fun s hz h0 h1 => h.1 s ⟨hz, by simpa using h0, by simpa using h1⟩, h.2.1⟩

theorem all_valid {l : List MainCert} (h : l.all (fun x => decide (FineValid x)) = true) :
    ∀ x ∈ l, FineValid x := fun x hx => of_decide_eq_true (List.all_eq_true.mp h x hx)

/-- The table of the zeros up to `1000`. -/
noncomputable def table0 (h : Head1000.Certified) : RangeTable 649 ((0 : ℕ) : ℝ) ((1000 : ℕ) : ℝ) :=
  RvMData0Small.facts.table (certified0 h)

theorem positiveZeroCount_eq0 (h : Head1000.Certified) {T : ℝ} (hT : 0 < T) (h1 : T ≤ 1000) :
    Rosser1941.positiveZeroCount T = ((indicesBelow (table0 h).ordinate T).card : ℝ) := by
  rw [Rosser1941.positiveZeroCount_eq hT,
    RangeTable.N_le_eq_card (table0 h) Nat.cast_zero hT (by norm_num; linarith)]

theorem window (h : Head1000.Certified) {T : ℝ} (h1 : 100 ≤ T) (h2 : T ≤ 280) :
    |((indicesBelow (table0 h).ordinate T).card : ℝ) - rosserF T| < 1 := by
  have hv := all_valid RvMData0Small.valid
  have := window_of_checks RvMData0Small.facts (certified0 h) (a := 100) (b := 280)
    (base := 0) (c := 1) (K0 := 29) (K := 126) (by norm_num) (by norm_num)
    (cls := RvMData0Small.cls) (chs := RvMData0Small.chs)
    (cA := RvMData0Small.cA) (cB := RvMData0Small.cB) (by norm_num) RvMData0Small.len
    RvMData0Small.pair (fun x hx => hv x (by simp [hx])) (fun x hx => hv x (by simp [hx]))
    (hv _ (by simp)) (hv _ (by simp)) RvMData0Small.below RvMData0Small.above
    RvMData0Small.ends.1 RvMData0Small.ends.2.1 RvMData0Small.ends.2.2.1
    RvMData0Small.ends.2.2.2 (T := T) (by exact_mod_cast h1) (by exact_mod_cast h2)
  have key : ∀ x : ℝ, |((0 : ℕ) : ℝ) + x - rosserF T| < ((1 : ℕ) : ℝ) → |x - rosserF T| < 1 :=
    fun x hx => by simpa using hx
  exact key _ this

/-- **`ZeroCount.v1.rvm_error_small`**, for the project's count: `|N(t) − F(t)| < 1` for
`0 < t ≤ 280`, given the statements of `Zeros0to1000`. -/
theorem rvm_error_small (h : Head1000.Certified) (t : ℝ) (ht : 0 < t) (h280 : t ≤ 280) :
    |Rosser1941.positiveZeroCount t -
      (t / (2 * π) * log (t / (2 * π)) - t / (2 * π) + 7 / 8)| < 1 := by
  by_cases h100 : t ≤ 100
  · exact Rosser1941.zero_count_error_lt_one_to_100 t ht.le h100
  · rw [positiveZeroCount_eq0 h ht (by linarith)]
    exact window h (not_le.mp h100).le h280

end TernaryGoldbach.RSBounds.RvMSmall
