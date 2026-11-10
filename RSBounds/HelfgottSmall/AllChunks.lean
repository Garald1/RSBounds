import RSBounds.HelfgottSmall.Group.G00
import RSBounds.HelfgottSmall.Group.G01
import RSBounds.HelfgottSmall.Group.G02
import RSBounds.HelfgottSmall.Group.G03
import RSBounds.HelfgottSmall.Group.G04
import RSBounds.HelfgottSmall.Group.G05
import RSBounds.HelfgottSmall.Group.G06
import RSBounds.HelfgottSmall.Group.G07
import RSBounds.HelfgottSmall.Group.G08
import RSBounds.HelfgottSmall.Group.G09
import RSBounds.HelfgottSmall.Group.G10
import RSBounds.HelfgottSmall.Group.G11
import RSBounds.HelfgottSmall.Group.G12
import RSBounds.HelfgottSmall.Group.G13
import RSBounds.HelfgottSmall.Group.G14
import RSBounds.HelfgottSmall.Group.G15
import RSBounds.HelfgottSmall.Group.G16
import RSBounds.HelfgottSmall.Group.G17
import RSBounds.HelfgottSmall.Group.G18
import RSBounds.HelfgottSmall.Group.G19
import RSBounds.HelfgottSmall.Group.G20
import RSBounds.HelfgottSmall.Group.G21
import RSBounds.HelfgottSmall.Group.G22
import RSBounds.HelfgottSmall.Group.G23
import RSBounds.HelfgottSmall.Group.G24

/-!
# All chunks of the walk
-/

namespace RSBounds.HelfgottSmall

theorem chunkGood_all (i : Nat) (hi : i < 1250) : ChunkGood i := by
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
  if h4 : i < 250 then
    have e : i = 200 + (i - 200) := by omega
    exact e ▸ group_4 (i - 200) (by omega)
  else
  if h5 : i < 300 then
    have e : i = 250 + (i - 250) := by omega
    exact e ▸ group_5 (i - 250) (by omega)
  else
  if h6 : i < 350 then
    have e : i = 300 + (i - 300) := by omega
    exact e ▸ group_6 (i - 300) (by omega)
  else
  if h7 : i < 400 then
    have e : i = 350 + (i - 350) := by omega
    exact e ▸ group_7 (i - 350) (by omega)
  else
  if h8 : i < 450 then
    have e : i = 400 + (i - 400) := by omega
    exact e ▸ group_8 (i - 400) (by omega)
  else
  if h9 : i < 500 then
    have e : i = 450 + (i - 450) := by omega
    exact e ▸ group_9 (i - 450) (by omega)
  else
  if h10 : i < 550 then
    have e : i = 500 + (i - 500) := by omega
    exact e ▸ group_10 (i - 500) (by omega)
  else
  if h11 : i < 600 then
    have e : i = 550 + (i - 550) := by omega
    exact e ▸ group_11 (i - 550) (by omega)
  else
  if h12 : i < 650 then
    have e : i = 600 + (i - 600) := by omega
    exact e ▸ group_12 (i - 600) (by omega)
  else
  if h13 : i < 700 then
    have e : i = 650 + (i - 650) := by omega
    exact e ▸ group_13 (i - 650) (by omega)
  else
  if h14 : i < 750 then
    have e : i = 700 + (i - 700) := by omega
    exact e ▸ group_14 (i - 700) (by omega)
  else
  if h15 : i < 800 then
    have e : i = 750 + (i - 750) := by omega
    exact e ▸ group_15 (i - 750) (by omega)
  else
  if h16 : i < 850 then
    have e : i = 800 + (i - 800) := by omega
    exact e ▸ group_16 (i - 800) (by omega)
  else
  if h17 : i < 900 then
    have e : i = 850 + (i - 850) := by omega
    exact e ▸ group_17 (i - 850) (by omega)
  else
  if h18 : i < 950 then
    have e : i = 900 + (i - 900) := by omega
    exact e ▸ group_18 (i - 900) (by omega)
  else
  if h19 : i < 1000 then
    have e : i = 950 + (i - 950) := by omega
    exact e ▸ group_19 (i - 950) (by omega)
  else
  if h20 : i < 1050 then
    have e : i = 1000 + (i - 1000) := by omega
    exact e ▸ group_20 (i - 1000) (by omega)
  else
  if h21 : i < 1100 then
    have e : i = 1050 + (i - 1050) := by omega
    exact e ▸ group_21 (i - 1050) (by omega)
  else
  if h22 : i < 1150 then
    have e : i = 1100 + (i - 1100) := by omega
    exact e ▸ group_22 (i - 1100) (by omega)
  else
  if h23 : i < 1200 then
    have e : i = 1150 + (i - 1150) := by omega
    exact e ▸ group_23 (i - 1150) (by omega)
  else
  if h24 : i < 1250 then
    have e : i = 1200 + (i - 1200) := by omega
    exact e ▸ group_24 (i - 1200) (by omega)
  else
  exact absurd hi (by omega)

end RSBounds.HelfgottSmall
