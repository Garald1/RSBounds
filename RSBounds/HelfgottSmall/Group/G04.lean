import RSBounds.HelfgottSmall.Chunk.C0200
import RSBounds.HelfgottSmall.Chunk.C0201
import RSBounds.HelfgottSmall.Chunk.C0202
import RSBounds.HelfgottSmall.Chunk.C0203
import RSBounds.HelfgottSmall.Chunk.C0204
import RSBounds.HelfgottSmall.Chunk.C0205
import RSBounds.HelfgottSmall.Chunk.C0206
import RSBounds.HelfgottSmall.Chunk.C0207
import RSBounds.HelfgottSmall.Chunk.C0208
import RSBounds.HelfgottSmall.Chunk.C0209
import RSBounds.HelfgottSmall.Chunk.C0210
import RSBounds.HelfgottSmall.Chunk.C0211
import RSBounds.HelfgottSmall.Chunk.C0212
import RSBounds.HelfgottSmall.Chunk.C0213
import RSBounds.HelfgottSmall.Chunk.C0214
import RSBounds.HelfgottSmall.Chunk.C0215
import RSBounds.HelfgottSmall.Chunk.C0216
import RSBounds.HelfgottSmall.Chunk.C0217
import RSBounds.HelfgottSmall.Chunk.C0218
import RSBounds.HelfgottSmall.Chunk.C0219
import RSBounds.HelfgottSmall.Chunk.C0220
import RSBounds.HelfgottSmall.Chunk.C0221
import RSBounds.HelfgottSmall.Chunk.C0222
import RSBounds.HelfgottSmall.Chunk.C0223
import RSBounds.HelfgottSmall.Chunk.C0224
import RSBounds.HelfgottSmall.Chunk.C0225
import RSBounds.HelfgottSmall.Chunk.C0226
import RSBounds.HelfgottSmall.Chunk.C0227
import RSBounds.HelfgottSmall.Chunk.C0228
import RSBounds.HelfgottSmall.Chunk.C0229
import RSBounds.HelfgottSmall.Chunk.C0230
import RSBounds.HelfgottSmall.Chunk.C0231
import RSBounds.HelfgottSmall.Chunk.C0232
import RSBounds.HelfgottSmall.Chunk.C0233
import RSBounds.HelfgottSmall.Chunk.C0234
import RSBounds.HelfgottSmall.Chunk.C0235
import RSBounds.HelfgottSmall.Chunk.C0236
import RSBounds.HelfgottSmall.Chunk.C0237
import RSBounds.HelfgottSmall.Chunk.C0238
import RSBounds.HelfgottSmall.Chunk.C0239
import RSBounds.HelfgottSmall.Chunk.C0240
import RSBounds.HelfgottSmall.Chunk.C0241
import RSBounds.HelfgottSmall.Chunk.C0242
import RSBounds.HelfgottSmall.Chunk.C0243
import RSBounds.HelfgottSmall.Chunk.C0244
import RSBounds.HelfgottSmall.Chunk.C0245
import RSBounds.HelfgottSmall.Chunk.C0246
import RSBounds.HelfgottSmall.Chunk.C0247
import RSBounds.HelfgottSmall.Chunk.C0248
import RSBounds.HelfgottSmall.Chunk.C0249

/-! Walk chunks 200 to 249. -/

namespace RSBounds.HelfgottSmall

theorem group_4 (t : Nat) (ht : t < 50) : ChunkGood (200 + t) :=
  match t, ht with
  | 0, _ => chunk_200
  | 1, _ => chunk_201
  | 2, _ => chunk_202
  | 3, _ => chunk_203
  | 4, _ => chunk_204
  | 5, _ => chunk_205
  | 6, _ => chunk_206
  | 7, _ => chunk_207
  | 8, _ => chunk_208
  | 9, _ => chunk_209
  | 10, _ => chunk_210
  | 11, _ => chunk_211
  | 12, _ => chunk_212
  | 13, _ => chunk_213
  | 14, _ => chunk_214
  | 15, _ => chunk_215
  | 16, _ => chunk_216
  | 17, _ => chunk_217
  | 18, _ => chunk_218
  | 19, _ => chunk_219
  | 20, _ => chunk_220
  | 21, _ => chunk_221
  | 22, _ => chunk_222
  | 23, _ => chunk_223
  | 24, _ => chunk_224
  | 25, _ => chunk_225
  | 26, _ => chunk_226
  | 27, _ => chunk_227
  | 28, _ => chunk_228
  | 29, _ => chunk_229
  | 30, _ => chunk_230
  | 31, _ => chunk_231
  | 32, _ => chunk_232
  | 33, _ => chunk_233
  | 34, _ => chunk_234
  | 35, _ => chunk_235
  | 36, _ => chunk_236
  | 37, _ => chunk_237
  | 38, _ => chunk_238
  | 39, _ => chunk_239
  | 40, _ => chunk_240
  | 41, _ => chunk_241
  | 42, _ => chunk_242
  | 43, _ => chunk_243
  | 44, _ => chunk_244
  | 45, _ => chunk_245
  | 46, _ => chunk_246
  | 47, _ => chunk_247
  | 48, _ => chunk_248
  | 49, _ => chunk_249
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
