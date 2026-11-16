import RSBounds.HelfgottSmall.Chunk.C0000
import RSBounds.HelfgottSmall.Chunk.C0001
import RSBounds.HelfgottSmall.Chunk.C0002
import RSBounds.HelfgottSmall.Chunk.C0003
import RSBounds.HelfgottSmall.Chunk.C0004
import RSBounds.HelfgottSmall.Chunk.C0005
import RSBounds.HelfgottSmall.Chunk.C0006
import RSBounds.HelfgottSmall.Chunk.C0007
import RSBounds.HelfgottSmall.Chunk.C0008
import RSBounds.HelfgottSmall.Chunk.C0009
import RSBounds.HelfgottSmall.Chunk.C0010
import RSBounds.HelfgottSmall.Chunk.C0011
import RSBounds.HelfgottSmall.Chunk.C0012
import RSBounds.HelfgottSmall.Chunk.C0013
import RSBounds.HelfgottSmall.Chunk.C0014
import RSBounds.HelfgottSmall.Chunk.C0015
import RSBounds.HelfgottSmall.Chunk.C0016
import RSBounds.HelfgottSmall.Chunk.C0017
import RSBounds.HelfgottSmall.Chunk.C0018
import RSBounds.HelfgottSmall.Chunk.C0019
import RSBounds.HelfgottSmall.Chunk.C0020
import RSBounds.HelfgottSmall.Chunk.C0021
import RSBounds.HelfgottSmall.Chunk.C0022
import RSBounds.HelfgottSmall.Chunk.C0023
import RSBounds.HelfgottSmall.Chunk.C0024
import RSBounds.HelfgottSmall.Chunk.C0025
import RSBounds.HelfgottSmall.Chunk.C0026
import RSBounds.HelfgottSmall.Chunk.C0027
import RSBounds.HelfgottSmall.Chunk.C0028
import RSBounds.HelfgottSmall.Chunk.C0029
import RSBounds.HelfgottSmall.Chunk.C0030
import RSBounds.HelfgottSmall.Chunk.C0031
import RSBounds.HelfgottSmall.Chunk.C0032
import RSBounds.HelfgottSmall.Chunk.C0033
import RSBounds.HelfgottSmall.Chunk.C0034
import RSBounds.HelfgottSmall.Chunk.C0035
import RSBounds.HelfgottSmall.Chunk.C0036
import RSBounds.HelfgottSmall.Chunk.C0037
import RSBounds.HelfgottSmall.Chunk.C0038
import RSBounds.HelfgottSmall.Chunk.C0039
import RSBounds.HelfgottSmall.Chunk.C0040
import RSBounds.HelfgottSmall.Chunk.C0041
import RSBounds.HelfgottSmall.Chunk.C0042
import RSBounds.HelfgottSmall.Chunk.C0043
import RSBounds.HelfgottSmall.Chunk.C0044
import RSBounds.HelfgottSmall.Chunk.C0045
import RSBounds.HelfgottSmall.Chunk.C0046
import RSBounds.HelfgottSmall.Chunk.C0047
import RSBounds.HelfgottSmall.Chunk.C0048
import RSBounds.HelfgottSmall.Chunk.C0049

/-! Walk chunks 0 to 49. -/

namespace RSBounds.HelfgottSmall

theorem group_0 (t : Nat) (ht : t < 50) : ChunkGood (0 + t) :=
  match t, ht with
  | 0, _ => chunk_0
  | 1, _ => chunk_1
  | 2, _ => chunk_2
  | 3, _ => chunk_3
  | 4, _ => chunk_4
  | 5, _ => chunk_5
  | 6, _ => chunk_6
  | 7, _ => chunk_7
  | 8, _ => chunk_8
  | 9, _ => chunk_9
  | 10, _ => chunk_10
  | 11, _ => chunk_11
  | 12, _ => chunk_12
  | 13, _ => chunk_13
  | 14, _ => chunk_14
  | 15, _ => chunk_15
  | 16, _ => chunk_16
  | 17, _ => chunk_17
  | 18, _ => chunk_18
  | 19, _ => chunk_19
  | 20, _ => chunk_20
  | 21, _ => chunk_21
  | 22, _ => chunk_22
  | 23, _ => chunk_23
  | 24, _ => chunk_24
  | 25, _ => chunk_25
  | 26, _ => chunk_26
  | 27, _ => chunk_27
  | 28, _ => chunk_28
  | 29, _ => chunk_29
  | 30, _ => chunk_30
  | 31, _ => chunk_31
  | 32, _ => chunk_32
  | 33, _ => chunk_33
  | 34, _ => chunk_34
  | 35, _ => chunk_35
  | 36, _ => chunk_36
  | 37, _ => chunk_37
  | 38, _ => chunk_38
  | 39, _ => chunk_39
  | 40, _ => chunk_40
  | 41, _ => chunk_41
  | 42, _ => chunk_42
  | 43, _ => chunk_43
  | 44, _ => chunk_44
  | 45, _ => chunk_45
  | 46, _ => chunk_46
  | 47, _ => chunk_47
  | 48, _ => chunk_48
  | 49, _ => chunk_49
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
