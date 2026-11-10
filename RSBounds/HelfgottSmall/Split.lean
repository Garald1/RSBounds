import RSBounds.HelfgottSmall.States

/-!
# Joining consecutive walks

`chunkOK_split`: two successful walks, the second starting where the first ends, make one.
Used for chunk 0, which is checked in parts to bound the kernel's memory.
-/

namespace RSBounds.HelfgottSmall

theorem walk_add (f1 f2 : Nat) (st : St) :
    walk (f1 + f2) st = match walk f1 st with
      | none => none
      | some st' => walk f2 st' := by
  induction f1 generalizing st with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
    rw [Nat.succ_add]
    show (match step st with
      | none => none
      | some st' => walk (k + f2) st') = (match (match step st with
        | none => none
        | some st' => walk k st') with
      | none => none
      | some st' => walk f2 st')
    cases step st with
    | none => rfl
    | some st' => exact ih st'

theorem stEq_eq' {r st : St} (h : stEq r st = true) : r = st := by
  obtain ⟨n, psi, s, ia, a, l, b, ie, q, k⟩ := r
  obtain ⟨n', psi', s', ia', a', l', b', ie', q', k'⟩ := st
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

theorem stEq_self (st : St) : stEq st st = true := by
  obtain ⟨n, psi, s, ia, a, l, b, ie, q, k⟩ := st
  simp [stEq, Nat.beq_refl]

theorem chunkOK_split {f1 f2 : Nat} {st mid st' : St} (h1 : chunkOK f1 st mid = true)
    (h2 : chunkOK f2 mid st' = true) : chunkOK (f1 + f2) st st' = true := by
  have w1 : walk f1 st = some mid := by
    unfold chunkOK at h1
    split at h1
    · rename_i r hr
      rw [hr, stEq_eq' h1]
    · exact absurd h1 (by simp)
  have w2 : walk f2 mid = some st' := by
    unfold chunkOK at h2
    split at h2
    · rename_i r hr
      rw [hr, stEq_eq' h2]
    · exact absurd h2 (by simp)
  unfold chunkOK
  rw [walk_add, w1]
  show (match walk f2 mid with
    | some r => stEq r st'
    | none => false) = true
  rw [w2]
  exact stEq_self st'

end RSBounds.HelfgottSmall
