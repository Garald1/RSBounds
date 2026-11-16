/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Targets
import ZetaBridge.Statement

/-!
# The bridge's proposition is RSBounds' premise

`ZetaRH.FiniteRH`, the proposition that `ZetaBridge` proves at height `1894438.5122`, is the same
as `Goals.FiniteRH`, the premise of RSBounds' finite-RH results. This file imports neither `zeta`
nor any proof, so it can be checked without `zeta`'s prebuilt release.
-/

open TernaryGoldbach.RSBounds

theorem TernaryGoldbach.RSBounds.ZetaRH.finiteRH_eq_goals :
    ZetaRH.FiniteRH = Goals.FiniteRH := rfl
