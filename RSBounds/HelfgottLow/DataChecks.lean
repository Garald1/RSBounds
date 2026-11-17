import RSBounds.HelfgottLow.Defs

/-!
# Kernel checks of the walk's data
-/

namespace RSBounds.HelfgottLow

open RSBounds.HelfgottSmall (SC)

theorem anchors_chainOK : chainOK anchorsAll = true := by decide +kernel

theorem anchors_rOK : rOK anchorsAll = true := by decide +kernel

theorem anchors_head :
    anchorsAll.head? = some (2, 693147180800000, 693147180300000, 707106781186548) := by
  decide +kernel

theorem rho0_ok : RHO0 * RHO0 * (N0 + 1) ≤ SC * SC := by decide +kernel

end RSBounds.HelfgottLow
