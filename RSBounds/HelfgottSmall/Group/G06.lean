import RSBounds.HelfgottSmall.Chunk.C0300
import RSBounds.HelfgottSmall.Chunk.C0301
import RSBounds.HelfgottSmall.Chunk.C0302
import RSBounds.HelfgottSmall.Chunk.C0303
import RSBounds.HelfgottSmall.Chunk.C0304
import RSBounds.HelfgottSmall.Chunk.C0305
import RSBounds.HelfgottSmall.Chunk.C0306
import RSBounds.HelfgottSmall.Chunk.C0307
import RSBounds.HelfgottSmall.Chunk.C0308
import RSBounds.HelfgottSmall.Chunk.C0309
import RSBounds.HelfgottSmall.Chunk.C0310
import RSBounds.HelfgottSmall.Chunk.C0311
import RSBounds.HelfgottSmall.Chunk.C0312
import RSBounds.HelfgottSmall.Chunk.C0313
import RSBounds.HelfgottSmall.Chunk.C0314
import RSBounds.HelfgottSmall.Chunk.C0315
import RSBounds.HelfgottSmall.Chunk.C0316
import RSBounds.HelfgottSmall.Chunk.C0317
import RSBounds.HelfgottSmall.Chunk.C0318
import RSBounds.HelfgottSmall.Chunk.C0319
import RSBounds.HelfgottSmall.Chunk.C0320
import RSBounds.HelfgottSmall.Chunk.C0321
import RSBounds.HelfgottSmall.Chunk.C0322
import RSBounds.HelfgottSmall.Chunk.C0323
import RSBounds.HelfgottSmall.Chunk.C0324
import RSBounds.HelfgottSmall.Chunk.C0325
import RSBounds.HelfgottSmall.Chunk.C0326
import RSBounds.HelfgottSmall.Chunk.C0327
import RSBounds.HelfgottSmall.Chunk.C0328
import RSBounds.HelfgottSmall.Chunk.C0329
import RSBounds.HelfgottSmall.Chunk.C0330
import RSBounds.HelfgottSmall.Chunk.C0331
import RSBounds.HelfgottSmall.Chunk.C0332
import RSBounds.HelfgottSmall.Chunk.C0333
import RSBounds.HelfgottSmall.Chunk.C0334
import RSBounds.HelfgottSmall.Chunk.C0335
import RSBounds.HelfgottSmall.Chunk.C0336
import RSBounds.HelfgottSmall.Chunk.C0337
import RSBounds.HelfgottSmall.Chunk.C0338
import RSBounds.HelfgottSmall.Chunk.C0339
import RSBounds.HelfgottSmall.Chunk.C0340
import RSBounds.HelfgottSmall.Chunk.C0341
import RSBounds.HelfgottSmall.Chunk.C0342
import RSBounds.HelfgottSmall.Chunk.C0343
import RSBounds.HelfgottSmall.Chunk.C0344
import RSBounds.HelfgottSmall.Chunk.C0345
import RSBounds.HelfgottSmall.Chunk.C0346
import RSBounds.HelfgottSmall.Chunk.C0347
import RSBounds.HelfgottSmall.Chunk.C0348
import RSBounds.HelfgottSmall.Chunk.C0349

/-! Walk chunks 300 to 349. -/

namespace RSBounds.HelfgottSmall

theorem group_6 (t : Nat) (ht : t < 50) : ChunkGood (300 + t) :=
  match t, ht with
  | 0, _ => chunk_300
  | 1, _ => chunk_301
  | 2, _ => chunk_302
  | 3, _ => chunk_303
  | 4, _ => chunk_304
  | 5, _ => chunk_305
  | 6, _ => chunk_306
  | 7, _ => chunk_307
  | 8, _ => chunk_308
  | 9, _ => chunk_309
  | 10, _ => chunk_310
  | 11, _ => chunk_311
  | 12, _ => chunk_312
  | 13, _ => chunk_313
  | 14, _ => chunk_314
  | 15, _ => chunk_315
  | 16, _ => chunk_316
  | 17, _ => chunk_317
  | 18, _ => chunk_318
  | 19, _ => chunk_319
  | 20, _ => chunk_320
  | 21, _ => chunk_321
  | 22, _ => chunk_322
  | 23, _ => chunk_323
  | 24, _ => chunk_324
  | 25, _ => chunk_325
  | 26, _ => chunk_326
  | 27, _ => chunk_327
  | 28, _ => chunk_328
  | 29, _ => chunk_329
  | 30, _ => chunk_330
  | 31, _ => chunk_331
  | 32, _ => chunk_332
  | 33, _ => chunk_333
  | 34, _ => chunk_334
  | 35, _ => chunk_335
  | 36, _ => chunk_336
  | 37, _ => chunk_337
  | 38, _ => chunk_338
  | 39, _ => chunk_339
  | 40, _ => chunk_340
  | 41, _ => chunk_341
  | 42, _ => chunk_342
  | 43, _ => chunk_343
  | 44, _ => chunk_344
  | 45, _ => chunk_345
  | 46, _ => chunk_346
  | 47, _ => chunk_347
  | 48, _ => chunk_348
  | 49, _ => chunk_349
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
