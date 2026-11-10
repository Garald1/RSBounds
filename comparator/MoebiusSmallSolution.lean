/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.MoebiusInputs
import MoebiusCert.Agg.Ms

/-! (m) alone, with the proof of `MoebiusCert.Final` (whose closure also contains (M)). -/

namespace TernaryGoldbach.RSBounds.MoebiusInputs

open MoebiusCert

theorem smallMoebiusSum : SmallMoebiusSum := by
  intro n hn1 hn2
  obtain ⟨hb, -⟩ := MoebiusCert.Agg.msAll (by simp [MsInv, msum])
  exact hb n (by omega) (by omega) hn1

end TernaryGoldbach.RSBounds.MoebiusInputs
