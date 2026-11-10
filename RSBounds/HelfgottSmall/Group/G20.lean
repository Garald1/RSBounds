import RSBounds.HelfgottSmall.Chunk.C1000
import RSBounds.HelfgottSmall.Chunk.C1001
import RSBounds.HelfgottSmall.Chunk.C1002
import RSBounds.HelfgottSmall.Chunk.C1003
import RSBounds.HelfgottSmall.Chunk.C1004
import RSBounds.HelfgottSmall.Chunk.C1005
import RSBounds.HelfgottSmall.Chunk.C1006
import RSBounds.HelfgottSmall.Chunk.C1007
import RSBounds.HelfgottSmall.Chunk.C1008
import RSBounds.HelfgottSmall.Chunk.C1009
import RSBounds.HelfgottSmall.Chunk.C1010
import RSBounds.HelfgottSmall.Chunk.C1011
import RSBounds.HelfgottSmall.Chunk.C1012
import RSBounds.HelfgottSmall.Chunk.C1013
import RSBounds.HelfgottSmall.Chunk.C1014
import RSBounds.HelfgottSmall.Chunk.C1015
import RSBounds.HelfgottSmall.Chunk.C1016
import RSBounds.HelfgottSmall.Chunk.C1017
import RSBounds.HelfgottSmall.Chunk.C1018
import RSBounds.HelfgottSmall.Chunk.C1019
import RSBounds.HelfgottSmall.Chunk.C1020
import RSBounds.HelfgottSmall.Chunk.C1021
import RSBounds.HelfgottSmall.Chunk.C1022
import RSBounds.HelfgottSmall.Chunk.C1023
import RSBounds.HelfgottSmall.Chunk.C1024
import RSBounds.HelfgottSmall.Chunk.C1025
import RSBounds.HelfgottSmall.Chunk.C1026
import RSBounds.HelfgottSmall.Chunk.C1027
import RSBounds.HelfgottSmall.Chunk.C1028
import RSBounds.HelfgottSmall.Chunk.C1029
import RSBounds.HelfgottSmall.Chunk.C1030
import RSBounds.HelfgottSmall.Chunk.C1031
import RSBounds.HelfgottSmall.Chunk.C1032
import RSBounds.HelfgottSmall.Chunk.C1033
import RSBounds.HelfgottSmall.Chunk.C1034
import RSBounds.HelfgottSmall.Chunk.C1035
import RSBounds.HelfgottSmall.Chunk.C1036
import RSBounds.HelfgottSmall.Chunk.C1037
import RSBounds.HelfgottSmall.Chunk.C1038
import RSBounds.HelfgottSmall.Chunk.C1039
import RSBounds.HelfgottSmall.Chunk.C1040
import RSBounds.HelfgottSmall.Chunk.C1041
import RSBounds.HelfgottSmall.Chunk.C1042
import RSBounds.HelfgottSmall.Chunk.C1043
import RSBounds.HelfgottSmall.Chunk.C1044
import RSBounds.HelfgottSmall.Chunk.C1045
import RSBounds.HelfgottSmall.Chunk.C1046
import RSBounds.HelfgottSmall.Chunk.C1047
import RSBounds.HelfgottSmall.Chunk.C1048
import RSBounds.HelfgottSmall.Chunk.C1049

/-! Walk chunks 1000 to 1049. -/

namespace RSBounds.HelfgottSmall

theorem group_20 (t : Nat) (ht : t < 50) : ChunkGood (1000 + t) :=
  match t, ht with
  | 0, _ => chunk_1000
  | 1, _ => chunk_1001
  | 2, _ => chunk_1002
  | 3, _ => chunk_1003
  | 4, _ => chunk_1004
  | 5, _ => chunk_1005
  | 6, _ => chunk_1006
  | 7, _ => chunk_1007
  | 8, _ => chunk_1008
  | 9, _ => chunk_1009
  | 10, _ => chunk_1010
  | 11, _ => chunk_1011
  | 12, _ => chunk_1012
  | 13, _ => chunk_1013
  | 14, _ => chunk_1014
  | 15, _ => chunk_1015
  | 16, _ => chunk_1016
  | 17, _ => chunk_1017
  | 18, _ => chunk_1018
  | 19, _ => chunk_1019
  | 20, _ => chunk_1020
  | 21, _ => chunk_1021
  | 22, _ => chunk_1022
  | 23, _ => chunk_1023
  | 24, _ => chunk_1024
  | 25, _ => chunk_1025
  | 26, _ => chunk_1026
  | 27, _ => chunk_1027
  | 28, _ => chunk_1028
  | 29, _ => chunk_1029
  | 30, _ => chunk_1030
  | 31, _ => chunk_1031
  | 32, _ => chunk_1032
  | 33, _ => chunk_1033
  | 34, _ => chunk_1034
  | 35, _ => chunk_1035
  | 36, _ => chunk_1036
  | 37, _ => chunk_1037
  | 38, _ => chunk_1038
  | 39, _ => chunk_1039
  | 40, _ => chunk_1040
  | 41, _ => chunk_1041
  | 42, _ => chunk_1042
  | 43, _ => chunk_1043
  | 44, _ => chunk_1044
  | 45, _ => chunk_1045
  | 46, _ => chunk_1046
  | 47, _ => chunk_1047
  | 48, _ => chunk_1048
  | 49, _ => chunk_1049
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
