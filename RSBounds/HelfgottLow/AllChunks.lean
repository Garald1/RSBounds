import RSBounds.HelfgottLow.Group.G00
import RSBounds.HelfgottLow.Group.G01
import RSBounds.HelfgottLow.Group.G02
import RSBounds.HelfgottLow.Group.G03

/-!
# All chunks of the walk
-/

namespace RSBounds.HelfgottLow

theorem chunkGood_all (i : Nat) (hi : i < NCH) : ChunkGood i := by
  have hi' : i < 200 := hi
  if h0 : i < 50 then
    have e : i = 0 + (i - 0) := by omega
    exact e ▸ group_0 (i - 0) (by omega)
  else
  if h1 : i < 100 then
    have e : i = 50 + (i - 50) := by omega
    exact e ▸ group_1 (i - 50) (by omega)
  else
  if h2 : i < 150 then
    have e : i = 100 + (i - 100) := by omega
    exact e ▸ group_2 (i - 100) (by omega)
  else
  if h3 : i < 200 then
    have e : i = 150 + (i - 150) := by omega
    exact e ▸ group_3 (i - 150) (by omega)
  else
  exact absurd hi' (by omega)

end RSBounds.HelfgottLow
