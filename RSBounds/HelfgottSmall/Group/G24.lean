import RSBounds.HelfgottSmall.Chunk.C1200
import RSBounds.HelfgottSmall.Chunk.C1201
import RSBounds.HelfgottSmall.Chunk.C1202
import RSBounds.HelfgottSmall.Chunk.C1203
import RSBounds.HelfgottSmall.Chunk.C1204
import RSBounds.HelfgottSmall.Chunk.C1205
import RSBounds.HelfgottSmall.Chunk.C1206
import RSBounds.HelfgottSmall.Chunk.C1207
import RSBounds.HelfgottSmall.Chunk.C1208
import RSBounds.HelfgottSmall.Chunk.C1209
import RSBounds.HelfgottSmall.Chunk.C1210
import RSBounds.HelfgottSmall.Chunk.C1211
import RSBounds.HelfgottSmall.Chunk.C1212
import RSBounds.HelfgottSmall.Chunk.C1213
import RSBounds.HelfgottSmall.Chunk.C1214
import RSBounds.HelfgottSmall.Chunk.C1215
import RSBounds.HelfgottSmall.Chunk.C1216
import RSBounds.HelfgottSmall.Chunk.C1217
import RSBounds.HelfgottSmall.Chunk.C1218
import RSBounds.HelfgottSmall.Chunk.C1219
import RSBounds.HelfgottSmall.Chunk.C1220
import RSBounds.HelfgottSmall.Chunk.C1221
import RSBounds.HelfgottSmall.Chunk.C1222
import RSBounds.HelfgottSmall.Chunk.C1223
import RSBounds.HelfgottSmall.Chunk.C1224
import RSBounds.HelfgottSmall.Chunk.C1225
import RSBounds.HelfgottSmall.Chunk.C1226
import RSBounds.HelfgottSmall.Chunk.C1227
import RSBounds.HelfgottSmall.Chunk.C1228
import RSBounds.HelfgottSmall.Chunk.C1229
import RSBounds.HelfgottSmall.Chunk.C1230
import RSBounds.HelfgottSmall.Chunk.C1231
import RSBounds.HelfgottSmall.Chunk.C1232
import RSBounds.HelfgottSmall.Chunk.C1233
import RSBounds.HelfgottSmall.Chunk.C1234
import RSBounds.HelfgottSmall.Chunk.C1235
import RSBounds.HelfgottSmall.Chunk.C1236
import RSBounds.HelfgottSmall.Chunk.C1237
import RSBounds.HelfgottSmall.Chunk.C1238
import RSBounds.HelfgottSmall.Chunk.C1239
import RSBounds.HelfgottSmall.Chunk.C1240
import RSBounds.HelfgottSmall.Chunk.C1241
import RSBounds.HelfgottSmall.Chunk.C1242
import RSBounds.HelfgottSmall.Chunk.C1243
import RSBounds.HelfgottSmall.Chunk.C1244
import RSBounds.HelfgottSmall.Chunk.C1245
import RSBounds.HelfgottSmall.Chunk.C1246
import RSBounds.HelfgottSmall.Chunk.C1247
import RSBounds.HelfgottSmall.Chunk.C1248
import RSBounds.HelfgottSmall.Chunk.C1249

/-! Walk chunks 1200 to 1249. -/

namespace RSBounds.HelfgottSmall

theorem group_24 (t : Nat) (ht : t < 50) : ChunkGood (1200 + t) :=
  match t, ht with
  | 0, _ => chunk_1200
  | 1, _ => chunk_1201
  | 2, _ => chunk_1202
  | 3, _ => chunk_1203
  | 4, _ => chunk_1204
  | 5, _ => chunk_1205
  | 6, _ => chunk_1206
  | 7, _ => chunk_1207
  | 8, _ => chunk_1208
  | 9, _ => chunk_1209
  | 10, _ => chunk_1210
  | 11, _ => chunk_1211
  | 12, _ => chunk_1212
  | 13, _ => chunk_1213
  | 14, _ => chunk_1214
  | 15, _ => chunk_1215
  | 16, _ => chunk_1216
  | 17, _ => chunk_1217
  | 18, _ => chunk_1218
  | 19, _ => chunk_1219
  | 20, _ => chunk_1220
  | 21, _ => chunk_1221
  | 22, _ => chunk_1222
  | 23, _ => chunk_1223
  | 24, _ => chunk_1224
  | 25, _ => chunk_1225
  | 26, _ => chunk_1226
  | 27, _ => chunk_1227
  | 28, _ => chunk_1228
  | 29, _ => chunk_1229
  | 30, _ => chunk_1230
  | 31, _ => chunk_1231
  | 32, _ => chunk_1232
  | 33, _ => chunk_1233
  | 34, _ => chunk_1234
  | 35, _ => chunk_1235
  | 36, _ => chunk_1236
  | 37, _ => chunk_1237
  | 38, _ => chunk_1238
  | 39, _ => chunk_1239
  | 40, _ => chunk_1240
  | 41, _ => chunk_1241
  | 42, _ => chunk_1242
  | 43, _ => chunk_1243
  | 44, _ => chunk_1244
  | 45, _ => chunk_1245
  | 46, _ => chunk_1246
  | 47, _ => chunk_1247
  | 48, _ => chunk_1248
  | 49, _ => chunk_1249
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
