/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The statement proved by the bridge

A verbatim copy of `TernaryGoldbach.RSBounds.Goals.FiniteRH` from `RSBounds/Targets.lean`.

The copy is needed because the bridge must be a `module`: a file that is not a `module` loads the
private part of everything it imports, and `zeta`'s prebuilt release ships those parts compressed
(Lean reports "invalid header"). A `module`, in turn, cannot import `RSBounds.Targets`, which is not
one. `ZetaBridge.Check` confirms in Lean that the copy and the original are the same proposition.
-/

@[expose] public section

namespace TernaryGoldbach.RSBounds.ZetaRH

/-- Same as `TernaryGoldbach.RSBounds.Goals.FiniteRH`; see `ZetaBridge.Check`. -/
def FiniteRH (A : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    |ρ.im| ≤ A → ρ.re = 1 / 2

end TernaryGoldbach.RSBounds.ZetaRH
