/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Targets
import Zeta.Main

/-!
# Finite RH at Rosser–Schoenfeld's height, from a kernel-checked zero verification

S. Mercuri and B. Mehta (`smmercuri/zeta`, tag `v1-1.8956e6`) prove in Lean, with only the
standard axioms, `Zeta.riemannHypothesisUpTo_1895609`: every zero `s` of `riemannZeta` with
`|s.im| < 1895609`, other than the trivial zeros and `s = 1`, has real part `1/2`.

That statement gives `Goals.FiniteRH A` for every `A < 1895609`, in particular at
Rosser–Schoenfeld's height `1894438.5122`. This is the premise, the same constant from
`RSBounds.Targets`, of RSBounds' RS75, Schoenfeld 1976, (2.14), (2.17) and Ramaré results, such as
`TernaryGoldbach.RSBounds.Moebius003.ramareMoebius_of_finiteRH`. See `zeta-bridge/README.md` for why
the two are not yet combined in one file.
-/

namespace TernaryGoldbach.RSBounds.ZetaRH

open Goals

/-- `Goals.FiniteRH A` for every `A < 1895609`, from `Zeta.riemannHypothesisUpTo_1895609`. -/
theorem finiteRH_of_lt {A : ℝ} (hA : A < 1895609) : FiniteRH A := by
  intro ρ hz h0 h1 hρ
  refine Zeta.riemannHypothesisUpTo_1895609 ρ hz ?_ ?_ (lt_of_le_of_lt hρ hA)
  · rintro ⟨n, rfl⟩
    have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at h0
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · rintro rfl
    simp at h1

/-- Finite RH up to Rosser–Schoenfeld's height `1894438.5122`, with no hypothesis. -/
theorem finiteRH_rs75 : FiniteRH 1894438.5122 :=
  finiteRH_of_lt (by norm_num)

end TernaryGoldbach.RSBounds.ZetaRH

/--
info: 'TernaryGoldbach.RSBounds.ZetaRH.finiteRH_rs75' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TernaryGoldbach.RSBounds.ZetaRH.finiteRH_rs75
