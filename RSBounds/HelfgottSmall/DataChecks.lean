import RSBounds.HelfgottSmall.Defs

/-!
# Kernel checks of the walk's data
-/

namespace RSBounds.HelfgottSmall

theorem bigP_eq : smallD.prod = bigP := by decide +kernel

theorem anchors_chainOK : chainOK anchorsAll = true := by decide +kernel

theorem anchors_head : anchorsAll.head? = some (2, 693147180800000) := by decide +kernel

theorem events_sortedStrict : sortedStrict eventsAll = true := by decide +kernel

theorem events_complete : eventsComplete = true := by decide +kernel

theorem smallD_le (m : Nat) (hm : m ∈ smallD) : m ≤ 5000 := by
  simp only [smallD, List.mem_filter, List.mem_range] at hm
  omega

end RSBounds.HelfgottSmall
