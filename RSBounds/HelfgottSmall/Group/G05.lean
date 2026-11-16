import RSBounds.HelfgottSmall.Chunk.C0250
import RSBounds.HelfgottSmall.Chunk.C0251
import RSBounds.HelfgottSmall.Chunk.C0252
import RSBounds.HelfgottSmall.Chunk.C0253
import RSBounds.HelfgottSmall.Chunk.C0254
import RSBounds.HelfgottSmall.Chunk.C0255
import RSBounds.HelfgottSmall.Chunk.C0256
import RSBounds.HelfgottSmall.Chunk.C0257
import RSBounds.HelfgottSmall.Chunk.C0258
import RSBounds.HelfgottSmall.Chunk.C0259
import RSBounds.HelfgottSmall.Chunk.C0260
import RSBounds.HelfgottSmall.Chunk.C0261
import RSBounds.HelfgottSmall.Chunk.C0262
import RSBounds.HelfgottSmall.Chunk.C0263
import RSBounds.HelfgottSmall.Chunk.C0264
import RSBounds.HelfgottSmall.Chunk.C0265
import RSBounds.HelfgottSmall.Chunk.C0266
import RSBounds.HelfgottSmall.Chunk.C0267
import RSBounds.HelfgottSmall.Chunk.C0268
import RSBounds.HelfgottSmall.Chunk.C0269
import RSBounds.HelfgottSmall.Chunk.C0270
import RSBounds.HelfgottSmall.Chunk.C0271
import RSBounds.HelfgottSmall.Chunk.C0272
import RSBounds.HelfgottSmall.Chunk.C0273
import RSBounds.HelfgottSmall.Chunk.C0274
import RSBounds.HelfgottSmall.Chunk.C0275
import RSBounds.HelfgottSmall.Chunk.C0276
import RSBounds.HelfgottSmall.Chunk.C0277
import RSBounds.HelfgottSmall.Chunk.C0278
import RSBounds.HelfgottSmall.Chunk.C0279
import RSBounds.HelfgottSmall.Chunk.C0280
import RSBounds.HelfgottSmall.Chunk.C0281
import RSBounds.HelfgottSmall.Chunk.C0282
import RSBounds.HelfgottSmall.Chunk.C0283
import RSBounds.HelfgottSmall.Chunk.C0284
import RSBounds.HelfgottSmall.Chunk.C0285
import RSBounds.HelfgottSmall.Chunk.C0286
import RSBounds.HelfgottSmall.Chunk.C0287
import RSBounds.HelfgottSmall.Chunk.C0288
import RSBounds.HelfgottSmall.Chunk.C0289
import RSBounds.HelfgottSmall.Chunk.C0290
import RSBounds.HelfgottSmall.Chunk.C0291
import RSBounds.HelfgottSmall.Chunk.C0292
import RSBounds.HelfgottSmall.Chunk.C0293
import RSBounds.HelfgottSmall.Chunk.C0294
import RSBounds.HelfgottSmall.Chunk.C0295
import RSBounds.HelfgottSmall.Chunk.C0296
import RSBounds.HelfgottSmall.Chunk.C0297
import RSBounds.HelfgottSmall.Chunk.C0298
import RSBounds.HelfgottSmall.Chunk.C0299

/-! Walk chunks 250 to 299. -/

namespace RSBounds.HelfgottSmall

theorem group_5 (t : Nat) (ht : t < 50) : ChunkGood (250 + t) :=
  match t, ht with
  | 0, _ => chunk_250
  | 1, _ => chunk_251
  | 2, _ => chunk_252
  | 3, _ => chunk_253
  | 4, _ => chunk_254
  | 5, _ => chunk_255
  | 6, _ => chunk_256
  | 7, _ => chunk_257
  | 8, _ => chunk_258
  | 9, _ => chunk_259
  | 10, _ => chunk_260
  | 11, _ => chunk_261
  | 12, _ => chunk_262
  | 13, _ => chunk_263
  | 14, _ => chunk_264
  | 15, _ => chunk_265
  | 16, _ => chunk_266
  | 17, _ => chunk_267
  | 18, _ => chunk_268
  | 19, _ => chunk_269
  | 20, _ => chunk_270
  | 21, _ => chunk_271
  | 22, _ => chunk_272
  | 23, _ => chunk_273
  | 24, _ => chunk_274
  | 25, _ => chunk_275
  | 26, _ => chunk_276
  | 27, _ => chunk_277
  | 28, _ => chunk_278
  | 29, _ => chunk_279
  | 30, _ => chunk_280
  | 31, _ => chunk_281
  | 32, _ => chunk_282
  | 33, _ => chunk_283
  | 34, _ => chunk_284
  | 35, _ => chunk_285
  | 36, _ => chunk_286
  | 37, _ => chunk_287
  | 38, _ => chunk_288
  | 39, _ => chunk_289
  | 40, _ => chunk_290
  | 41, _ => chunk_291
  | 42, _ => chunk_292
  | 43, _ => chunk_293
  | 44, _ => chunk_294
  | 45, _ => chunk_295
  | 46, _ => chunk_296
  | 47, _ => chunk_297
  | 48, _ => chunk_298
  | 49, _ => chunk_299
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
