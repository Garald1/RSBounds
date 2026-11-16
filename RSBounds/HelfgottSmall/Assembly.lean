import RSBounds.HelfgottSmall.Walk
import RSBounds.HelfgottSmall.States

/-!
# From the chunks to every position

If every chunk checks out, the walk goes from `stateOf 0` (position 2) to `stateOf 1250`
(position 25 000 001), so (2.14) and (2.17) hold at every integer where they apply.
-/

namespace RSBounds.HelfgottSmall

open Real Finset ArithmeticFunction

theorem stateOf_zero : stateOf 0 = (2, 0, 0, 0, 2, 693147180800000, 3, 0, 4, 2) := rfl

theorem stateOf_last : (stateOf 1250).1 = 25000001 := by decide +kernel

theorem anchor_two_mem : ((2 : ℕ), (693147180800000 : ℕ)) ∈ anchorsAll := by
  have h := anchors_head
  cases hL : anchorsAll with
  | nil => rw [hL] at h; simp at h
  | cons x t =>
    rw [hL] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    rw [h]
    exact List.mem_cons_self

theorem inv_zero : Inv (stateOf 0) := by
  rw [stateOf_zero]
  refine ⟨le_rfl, ?_, ?_, anchor_two_mem, rfl, rfl, Or.inl (by norm_num), fun j hj => by omega⟩
  · have : psiS (2 - 1) = 0 := by simp [psiS]
    rw [this]; simp
  · have : sS (2 - 1) = 0 := by simp [sS]
    rw [this]; simp

theorem reach (h : ∀ i < 1250, ChunkGood i) :
    ∀ i ≤ 1250, Inv (stateOf i) ∧ ∀ m, 2 ≤ m → m < (stateOf i).1 → GoodAt m := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨inv_zero, fun m h1 h2 => ?_⟩
    rw [stateOf_zero] at h2
    simp only at h2
    omega
  | succ i ih =>
    intro hi
    obtain ⟨hI, hG⟩ := ih (by omega)
    have hw := walk_of_chunkOK (h i (by omega))
    obtain ⟨hI', hn', hG'⟩ := walk_inv _ _ _ hI hw
    refine ⟨hI', fun m h1 h2 => ?_⟩
    rcases Nat.lt_or_ge m (stateOf i).1 with hm | hm
    · exact hG m h1 hm
    · exact hG' m hm (by omega)

theorem goodAt_all (h : ∀ i < 1250, ChunkGood i) (m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ 25000000) :
    GoodAt m :=
  (reach h 1250 le_rfl).2 m h1 (by rw [stateOf_last]; omega)

end RSBounds.HelfgottSmall
