import RSBounds.HelfgottLow.Walk
import RSBounds.HelfgottLow.States

/-!
# From the chunks to every position

If every chunk checks out, the walk goes from `attach (extOf 0)` (position 2) to
`attach (extOf NCH)` (position `N0 + 1`), so (2.16), (2.18) and (2.19) hold at every integer
`2 ≤ m ≤ N0` where they apply, and the closing check bounds `bS N0`.
-/

namespace RSBounds.HelfgottLow

open Real Finset ArithmeticFunction
open RSBounds.HelfgottSmall (SC SC_pos eventOf psiS sS)

theorem extOf_zero : extOf 0 = (2, 0, 0, 0, 0, 0, 0, 0) := rfl

theorem extOf_last_n : (extOf NCH).1 = N0 + 1 := by decide +kernel

theorem finalB_last : finalB (extOf NCH).2.1 (extOf NCH).2.2.2.1 = true := by decide +kernel

theorem attach_psi_t (e : Ext) : (attach e).psi = e.2.1 ∧ (attach e).t = e.2.2.2.1 := by
  obtain ⟨n, psi, s, t, d, ia, ja, ie⟩ := e
  exact ⟨rfl, rfl⟩

theorem inv_start : Inv (attach (2, 0, 0, 0, 0, 0, 0, 0)) := by
  have h0 : (anchorsAll.getD 0 dflt).1 ≠ 0 := by decide +kernel
  have hA := anchor_good (getD_mem h0)
  have hdrop : ∀ x ∈ anchorsAll.drop (0 + 1), Good x :=
    fun x hx => anchor_good (List.mem_of_mem_drop hx)
  have hq : (eventOf 0).1 = 4 := by decide +kernel
  have hA' := hA
  obtain ⟨⟨h2, _, hlo⟩, _⟩ := hA'
  have hSC := SC_pos
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, hA, hdrop, ⟨h2, hlo⟩, hdrop, rfl, Or.inl ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · show psiS 1 ≤ ((0 : ℕ) : ℝ) / SC
    simp [psiS]
  · show sS 1 ≤ ((0 : ℕ) : ℝ) / SC
    simp [sS]
  · show tS 1 ≤ ((0 : ℕ) : ℝ) / SC
    simp [tS]
  · show bS 1 ≤ ((0 : ℕ) : ℝ) / SC - RHO0 / SC * (((0 : ℕ) : ℝ) / SC)
    simp [bS]
  · show wS 0 1 ≤ ((0 : ℕ) : ℝ) / (SC : ℝ) ^ 2
    rw [wS, show (Ioc 0 1 : Finset ℕ) = {1} by decide, Finset.sum_singleton, gS_one]
    simp
  · show 2 ≤ (eventOf 0).1
    rw [hq]
    norm_num

theorem reach (h : ∀ i < NCH, ChunkGood i) :
    ∀ i ≤ NCH, Inv (attach (extOf i)) ∧ ∀ m, 2 ≤ m → m < (extOf i).1 → GoodAt m := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [extOf_zero]
    refine ⟨inv_start, fun m h1 h2 => ?_⟩
    simp only at h2
    omega
  | succ i ih =>
    intro hi
    obtain ⟨hI, hG⟩ := ih (by omega)
    have hw := walk_of_chunkOK (h i (by omega))
    obtain ⟨hI', hn', hG'⟩ := walk_inv _ _ _ hI hw
    rw [attach_n, attach_n] at hn'
    rw [attach_n] at hG'
    refine ⟨hI', fun m h1 h2 => ?_⟩
    rcases Nat.lt_or_ge m (extOf i).1 with hm | hm
    · exact hG m h1 hm
    · exact hG' m hm (by omega)

theorem goodAt_all (h : ∀ i < NCH, ChunkGood i) (m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ N0) :
    GoodAt m :=
  (reach h NCH le_rfl).2 m h1 (by rw [extOf_last_n]; omega)

theorem finalB_spec {psi t : ℕ} (h : finalB psi t = true) :
    (t : ℝ) / SC - RHO0 / SC * (psi / SC) < 1.0004 * √(N0 : ℝ) := by
  unfold finalB at h
  set X : ℕ := SC * t - RHO0 * psi with hX
  have h' : 100000000 * X ^ 2 < 100080016 * N0 * SC ^ 4 := Nat.blt_eq.mp h
  have h'' : (100000000 : ℝ) * (X : ℝ) ^ 2 < 100080016 * N0 * (SC : ℝ) ^ 4 := by exact_mod_cast h'
  have hSC := SC_pos
  have hXge : (SC : ℝ) * t - RHO0 * psi ≤ X := by
    rcases le_or_gt (RHO0 * psi) (SC * t) with hle | hlt
    · have : (X : ℝ) = (SC : ℝ) * t - RHO0 * psi := by
        rw [hX]; push_cast [hle]; ring
      rw [this]
    · have : (SC : ℝ) * t < RHO0 * psi := by exact_mod_cast hlt
      have : (0 : ℝ) ≤ X := Nat.cast_nonneg _
      linarith
  have hX0 : (0 : ℝ) ≤ (X : ℝ) / (SC : ℝ) ^ 2 := by positivity
  have hY0 : (0 : ℝ) ≤ 1.0004 * √(N0 : ℝ) := by positivity
  have hsq : ((X : ℝ) / (SC : ℝ) ^ 2) ^ 2 < (1.0004 * √(N0 : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_pow, div_lt_iff₀ (by positivity)]
    nlinarith
  have hlt := (pow_lt_pow_iff_left₀ hX0 hY0 (by norm_num)).mp hsq
  have e : (t : ℝ) / SC - RHO0 / SC * (psi / SC) = ((SC : ℝ) * t - RHO0 * psi) / (SC : ℝ) ^ 2 := by
    field_simp
  rw [e]
  calc ((SC : ℝ) * t - RHO0 * psi) / (SC : ℝ) ^ 2 ≤ (X : ℝ) / (SC : ℝ) ^ 2 := by gcongr
    _ < 1.0004 * √(N0 : ℝ) := hlt

theorem bS_final (h : ∀ i < NCH, ChunkGood i) : bS N0 < 1.0004 * √(N0 : ℝ) := by
  have hI := (reach h NCH le_rfl).1
  have hb := hI.2.2.2.2.1
  rw [attach_n, extOf_last_n, (attach_psi_t _).1, (attach_psi_t _).2] at hb
  simp only [Nat.add_sub_cancel] at hb
  exact lt_of_le_of_lt hb (finalB_spec finalB_last)

end RSBounds.HelfgottLow
