import RSBounds.HelfgottSmall.Chunk.C1100
import RSBounds.HelfgottSmall.Chunk.C1101
import RSBounds.HelfgottSmall.Chunk.C1102
import RSBounds.HelfgottSmall.Chunk.C1103
import RSBounds.HelfgottSmall.Chunk.C1104
import RSBounds.HelfgottSmall.Chunk.C1105
import RSBounds.HelfgottSmall.Chunk.C1106
import RSBounds.HelfgottSmall.Chunk.C1107
import RSBounds.HelfgottSmall.Chunk.C1108
import RSBounds.HelfgottSmall.Chunk.C1109
import RSBounds.HelfgottSmall.Chunk.C1110
import RSBounds.HelfgottSmall.Chunk.C1111
import RSBounds.HelfgottSmall.Chunk.C1112
import RSBounds.HelfgottSmall.Chunk.C1113
import RSBounds.HelfgottSmall.Chunk.C1114
import RSBounds.HelfgottSmall.Chunk.C1115
import RSBounds.HelfgottSmall.Chunk.C1116
import RSBounds.HelfgottSmall.Chunk.C1117
import RSBounds.HelfgottSmall.Chunk.C1118
import RSBounds.HelfgottSmall.Chunk.C1119
import RSBounds.HelfgottSmall.Chunk.C1120
import RSBounds.HelfgottSmall.Chunk.C1121
import RSBounds.HelfgottSmall.Chunk.C1122
import RSBounds.HelfgottSmall.Chunk.C1123
import RSBounds.HelfgottSmall.Chunk.C1124
import RSBounds.HelfgottSmall.Chunk.C1125
import RSBounds.HelfgottSmall.Chunk.C1126
import RSBounds.HelfgottSmall.Chunk.C1127
import RSBounds.HelfgottSmall.Chunk.C1128
import RSBounds.HelfgottSmall.Chunk.C1129
import RSBounds.HelfgottSmall.Chunk.C1130
import RSBounds.HelfgottSmall.Chunk.C1131
import RSBounds.HelfgottSmall.Chunk.C1132
import RSBounds.HelfgottSmall.Chunk.C1133
import RSBounds.HelfgottSmall.Chunk.C1134
import RSBounds.HelfgottSmall.Chunk.C1135
import RSBounds.HelfgottSmall.Chunk.C1136
import RSBounds.HelfgottSmall.Chunk.C1137
import RSBounds.HelfgottSmall.Chunk.C1138
import RSBounds.HelfgottSmall.Chunk.C1139
import RSBounds.HelfgottSmall.Chunk.C1140
import RSBounds.HelfgottSmall.Chunk.C1141
import RSBounds.HelfgottSmall.Chunk.C1142
import RSBounds.HelfgottSmall.Chunk.C1143
import RSBounds.HelfgottSmall.Chunk.C1144
import RSBounds.HelfgottSmall.Chunk.C1145
import RSBounds.HelfgottSmall.Chunk.C1146
import RSBounds.HelfgottSmall.Chunk.C1147
import RSBounds.HelfgottSmall.Chunk.C1148
import RSBounds.HelfgottSmall.Chunk.C1149

/-! Walk chunks 1100 to 1149. -/

namespace RSBounds.HelfgottSmall

theorem group_22 (t : Nat) (ht : t < 50) : ChunkGood (1100 + t) :=
  match t, ht with
  | 0, _ => chunk_1100
  | 1, _ => chunk_1101
  | 2, _ => chunk_1102
  | 3, _ => chunk_1103
  | 4, _ => chunk_1104
  | 5, _ => chunk_1105
  | 6, _ => chunk_1106
  | 7, _ => chunk_1107
  | 8, _ => chunk_1108
  | 9, _ => chunk_1109
  | 10, _ => chunk_1110
  | 11, _ => chunk_1111
  | 12, _ => chunk_1112
  | 13, _ => chunk_1113
  | 14, _ => chunk_1114
  | 15, _ => chunk_1115
  | 16, _ => chunk_1116
  | 17, _ => chunk_1117
  | 18, _ => chunk_1118
  | 19, _ => chunk_1119
  | 20, _ => chunk_1120
  | 21, _ => chunk_1121
  | 22, _ => chunk_1122
  | 23, _ => chunk_1123
  | 24, _ => chunk_1124
  | 25, _ => chunk_1125
  | 26, _ => chunk_1126
  | 27, _ => chunk_1127
  | 28, _ => chunk_1128
  | 29, _ => chunk_1129
  | 30, _ => chunk_1130
  | 31, _ => chunk_1131
  | 32, _ => chunk_1132
  | 33, _ => chunk_1133
  | 34, _ => chunk_1134
  | 35, _ => chunk_1135
  | 36, _ => chunk_1136
  | 37, _ => chunk_1137
  | 38, _ => chunk_1138
  | 39, _ => chunk_1139
  | 40, _ => chunk_1140
  | 41, _ => chunk_1141
  | 42, _ => chunk_1142
  | 43, _ => chunk_1143
  | 44, _ => chunk_1144
  | 45, _ => chunk_1145
  | 46, _ => chunk_1146
  | 47, _ => chunk_1147
  | 48, _ => chunk_1148
  | 49, _ => chunk_1149
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
