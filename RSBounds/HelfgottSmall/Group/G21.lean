import RSBounds.HelfgottSmall.Chunk.C1050
import RSBounds.HelfgottSmall.Chunk.C1051
import RSBounds.HelfgottSmall.Chunk.C1052
import RSBounds.HelfgottSmall.Chunk.C1053
import RSBounds.HelfgottSmall.Chunk.C1054
import RSBounds.HelfgottSmall.Chunk.C1055
import RSBounds.HelfgottSmall.Chunk.C1056
import RSBounds.HelfgottSmall.Chunk.C1057
import RSBounds.HelfgottSmall.Chunk.C1058
import RSBounds.HelfgottSmall.Chunk.C1059
import RSBounds.HelfgottSmall.Chunk.C1060
import RSBounds.HelfgottSmall.Chunk.C1061
import RSBounds.HelfgottSmall.Chunk.C1062
import RSBounds.HelfgottSmall.Chunk.C1063
import RSBounds.HelfgottSmall.Chunk.C1064
import RSBounds.HelfgottSmall.Chunk.C1065
import RSBounds.HelfgottSmall.Chunk.C1066
import RSBounds.HelfgottSmall.Chunk.C1067
import RSBounds.HelfgottSmall.Chunk.C1068
import RSBounds.HelfgottSmall.Chunk.C1069
import RSBounds.HelfgottSmall.Chunk.C1070
import RSBounds.HelfgottSmall.Chunk.C1071
import RSBounds.HelfgottSmall.Chunk.C1072
import RSBounds.HelfgottSmall.Chunk.C1073
import RSBounds.HelfgottSmall.Chunk.C1074
import RSBounds.HelfgottSmall.Chunk.C1075
import RSBounds.HelfgottSmall.Chunk.C1076
import RSBounds.HelfgottSmall.Chunk.C1077
import RSBounds.HelfgottSmall.Chunk.C1078
import RSBounds.HelfgottSmall.Chunk.C1079
import RSBounds.HelfgottSmall.Chunk.C1080
import RSBounds.HelfgottSmall.Chunk.C1081
import RSBounds.HelfgottSmall.Chunk.C1082
import RSBounds.HelfgottSmall.Chunk.C1083
import RSBounds.HelfgottSmall.Chunk.C1084
import RSBounds.HelfgottSmall.Chunk.C1085
import RSBounds.HelfgottSmall.Chunk.C1086
import RSBounds.HelfgottSmall.Chunk.C1087
import RSBounds.HelfgottSmall.Chunk.C1088
import RSBounds.HelfgottSmall.Chunk.C1089
import RSBounds.HelfgottSmall.Chunk.C1090
import RSBounds.HelfgottSmall.Chunk.C1091
import RSBounds.HelfgottSmall.Chunk.C1092
import RSBounds.HelfgottSmall.Chunk.C1093
import RSBounds.HelfgottSmall.Chunk.C1094
import RSBounds.HelfgottSmall.Chunk.C1095
import RSBounds.HelfgottSmall.Chunk.C1096
import RSBounds.HelfgottSmall.Chunk.C1097
import RSBounds.HelfgottSmall.Chunk.C1098
import RSBounds.HelfgottSmall.Chunk.C1099

/-! Walk chunks 1050 to 1099. -/

namespace RSBounds.HelfgottSmall

theorem group_21 (t : Nat) (ht : t < 50) : ChunkGood (1050 + t) :=
  match t, ht with
  | 0, _ => chunk_1050
  | 1, _ => chunk_1051
  | 2, _ => chunk_1052
  | 3, _ => chunk_1053
  | 4, _ => chunk_1054
  | 5, _ => chunk_1055
  | 6, _ => chunk_1056
  | 7, _ => chunk_1057
  | 8, _ => chunk_1058
  | 9, _ => chunk_1059
  | 10, _ => chunk_1060
  | 11, _ => chunk_1061
  | 12, _ => chunk_1062
  | 13, _ => chunk_1063
  | 14, _ => chunk_1064
  | 15, _ => chunk_1065
  | 16, _ => chunk_1066
  | 17, _ => chunk_1067
  | 18, _ => chunk_1068
  | 19, _ => chunk_1069
  | 20, _ => chunk_1070
  | 21, _ => chunk_1071
  | 22, _ => chunk_1072
  | 23, _ => chunk_1073
  | 24, _ => chunk_1074
  | 25, _ => chunk_1075
  | 26, _ => chunk_1076
  | 27, _ => chunk_1077
  | 28, _ => chunk_1078
  | 29, _ => chunk_1079
  | 30, _ => chunk_1080
  | 31, _ => chunk_1081
  | 32, _ => chunk_1082
  | 33, _ => chunk_1083
  | 34, _ => chunk_1084
  | 35, _ => chunk_1085
  | 36, _ => chunk_1086
  | 37, _ => chunk_1087
  | 38, _ => chunk_1088
  | 39, _ => chunk_1089
  | 40, _ => chunk_1090
  | 41, _ => chunk_1091
  | 42, _ => chunk_1092
  | 43, _ => chunk_1093
  | 44, _ => chunk_1094
  | 45, _ => chunk_1095
  | 46, _ => chunk_1096
  | 47, _ => chunk_1097
  | 48, _ => chunk_1098
  | 49, _ => chunk_1099
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
