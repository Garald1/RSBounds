import RSBounds.HelfgottSmall.Chunk.C1150
import RSBounds.HelfgottSmall.Chunk.C1151
import RSBounds.HelfgottSmall.Chunk.C1152
import RSBounds.HelfgottSmall.Chunk.C1153
import RSBounds.HelfgottSmall.Chunk.C1154
import RSBounds.HelfgottSmall.Chunk.C1155
import RSBounds.HelfgottSmall.Chunk.C1156
import RSBounds.HelfgottSmall.Chunk.C1157
import RSBounds.HelfgottSmall.Chunk.C1158
import RSBounds.HelfgottSmall.Chunk.C1159
import RSBounds.HelfgottSmall.Chunk.C1160
import RSBounds.HelfgottSmall.Chunk.C1161
import RSBounds.HelfgottSmall.Chunk.C1162
import RSBounds.HelfgottSmall.Chunk.C1163
import RSBounds.HelfgottSmall.Chunk.C1164
import RSBounds.HelfgottSmall.Chunk.C1165
import RSBounds.HelfgottSmall.Chunk.C1166
import RSBounds.HelfgottSmall.Chunk.C1167
import RSBounds.HelfgottSmall.Chunk.C1168
import RSBounds.HelfgottSmall.Chunk.C1169
import RSBounds.HelfgottSmall.Chunk.C1170
import RSBounds.HelfgottSmall.Chunk.C1171
import RSBounds.HelfgottSmall.Chunk.C1172
import RSBounds.HelfgottSmall.Chunk.C1173
import RSBounds.HelfgottSmall.Chunk.C1174
import RSBounds.HelfgottSmall.Chunk.C1175
import RSBounds.HelfgottSmall.Chunk.C1176
import RSBounds.HelfgottSmall.Chunk.C1177
import RSBounds.HelfgottSmall.Chunk.C1178
import RSBounds.HelfgottSmall.Chunk.C1179
import RSBounds.HelfgottSmall.Chunk.C1180
import RSBounds.HelfgottSmall.Chunk.C1181
import RSBounds.HelfgottSmall.Chunk.C1182
import RSBounds.HelfgottSmall.Chunk.C1183
import RSBounds.HelfgottSmall.Chunk.C1184
import RSBounds.HelfgottSmall.Chunk.C1185
import RSBounds.HelfgottSmall.Chunk.C1186
import RSBounds.HelfgottSmall.Chunk.C1187
import RSBounds.HelfgottSmall.Chunk.C1188
import RSBounds.HelfgottSmall.Chunk.C1189
import RSBounds.HelfgottSmall.Chunk.C1190
import RSBounds.HelfgottSmall.Chunk.C1191
import RSBounds.HelfgottSmall.Chunk.C1192
import RSBounds.HelfgottSmall.Chunk.C1193
import RSBounds.HelfgottSmall.Chunk.C1194
import RSBounds.HelfgottSmall.Chunk.C1195
import RSBounds.HelfgottSmall.Chunk.C1196
import RSBounds.HelfgottSmall.Chunk.C1197
import RSBounds.HelfgottSmall.Chunk.C1198
import RSBounds.HelfgottSmall.Chunk.C1199

/-! Walk chunks 1150 to 1199. -/

namespace RSBounds.HelfgottSmall

theorem group_23 (t : Nat) (ht : t < 50) : ChunkGood (1150 + t) :=
  match t, ht with
  | 0, _ => chunk_1150
  | 1, _ => chunk_1151
  | 2, _ => chunk_1152
  | 3, _ => chunk_1153
  | 4, _ => chunk_1154
  | 5, _ => chunk_1155
  | 6, _ => chunk_1156
  | 7, _ => chunk_1157
  | 8, _ => chunk_1158
  | 9, _ => chunk_1159
  | 10, _ => chunk_1160
  | 11, _ => chunk_1161
  | 12, _ => chunk_1162
  | 13, _ => chunk_1163
  | 14, _ => chunk_1164
  | 15, _ => chunk_1165
  | 16, _ => chunk_1166
  | 17, _ => chunk_1167
  | 18, _ => chunk_1168
  | 19, _ => chunk_1169
  | 20, _ => chunk_1170
  | 21, _ => chunk_1171
  | 22, _ => chunk_1172
  | 23, _ => chunk_1173
  | 24, _ => chunk_1174
  | 25, _ => chunk_1175
  | 26, _ => chunk_1176
  | 27, _ => chunk_1177
  | 28, _ => chunk_1178
  | 29, _ => chunk_1179
  | 30, _ => chunk_1180
  | 31, _ => chunk_1181
  | 32, _ => chunk_1182
  | 33, _ => chunk_1183
  | 34, _ => chunk_1184
  | 35, _ => chunk_1185
  | 36, _ => chunk_1186
  | 37, _ => chunk_1187
  | 38, _ => chunk_1188
  | 39, _ => chunk_1189
  | 40, _ => chunk_1190
  | 41, _ => chunk_1191
  | 42, _ => chunk_1192
  | 43, _ => chunk_1193
  | 44, _ => chunk_1194
  | 45, _ => chunk_1195
  | 46, _ => chunk_1196
  | 47, _ => chunk_1197
  | 48, _ => chunk_1198
  | 49, _ => chunk_1199
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
