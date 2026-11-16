import RSBounds.HelfgottSmall.Chunk.C0350
import RSBounds.HelfgottSmall.Chunk.C0351
import RSBounds.HelfgottSmall.Chunk.C0352
import RSBounds.HelfgottSmall.Chunk.C0353
import RSBounds.HelfgottSmall.Chunk.C0354
import RSBounds.HelfgottSmall.Chunk.C0355
import RSBounds.HelfgottSmall.Chunk.C0356
import RSBounds.HelfgottSmall.Chunk.C0357
import RSBounds.HelfgottSmall.Chunk.C0358
import RSBounds.HelfgottSmall.Chunk.C0359
import RSBounds.HelfgottSmall.Chunk.C0360
import RSBounds.HelfgottSmall.Chunk.C0361
import RSBounds.HelfgottSmall.Chunk.C0362
import RSBounds.HelfgottSmall.Chunk.C0363
import RSBounds.HelfgottSmall.Chunk.C0364
import RSBounds.HelfgottSmall.Chunk.C0365
import RSBounds.HelfgottSmall.Chunk.C0366
import RSBounds.HelfgottSmall.Chunk.C0367
import RSBounds.HelfgottSmall.Chunk.C0368
import RSBounds.HelfgottSmall.Chunk.C0369
import RSBounds.HelfgottSmall.Chunk.C0370
import RSBounds.HelfgottSmall.Chunk.C0371
import RSBounds.HelfgottSmall.Chunk.C0372
import RSBounds.HelfgottSmall.Chunk.C0373
import RSBounds.HelfgottSmall.Chunk.C0374
import RSBounds.HelfgottSmall.Chunk.C0375
import RSBounds.HelfgottSmall.Chunk.C0376
import RSBounds.HelfgottSmall.Chunk.C0377
import RSBounds.HelfgottSmall.Chunk.C0378
import RSBounds.HelfgottSmall.Chunk.C0379
import RSBounds.HelfgottSmall.Chunk.C0380
import RSBounds.HelfgottSmall.Chunk.C0381
import RSBounds.HelfgottSmall.Chunk.C0382
import RSBounds.HelfgottSmall.Chunk.C0383
import RSBounds.HelfgottSmall.Chunk.C0384
import RSBounds.HelfgottSmall.Chunk.C0385
import RSBounds.HelfgottSmall.Chunk.C0386
import RSBounds.HelfgottSmall.Chunk.C0387
import RSBounds.HelfgottSmall.Chunk.C0388
import RSBounds.HelfgottSmall.Chunk.C0389
import RSBounds.HelfgottSmall.Chunk.C0390
import RSBounds.HelfgottSmall.Chunk.C0391
import RSBounds.HelfgottSmall.Chunk.C0392
import RSBounds.HelfgottSmall.Chunk.C0393
import RSBounds.HelfgottSmall.Chunk.C0394
import RSBounds.HelfgottSmall.Chunk.C0395
import RSBounds.HelfgottSmall.Chunk.C0396
import RSBounds.HelfgottSmall.Chunk.C0397
import RSBounds.HelfgottSmall.Chunk.C0398
import RSBounds.HelfgottSmall.Chunk.C0399

/-! Walk chunks 350 to 399. -/

namespace RSBounds.HelfgottSmall

theorem group_7 (t : Nat) (ht : t < 50) : ChunkGood (350 + t) :=
  match t, ht with
  | 0, _ => chunk_350
  | 1, _ => chunk_351
  | 2, _ => chunk_352
  | 3, _ => chunk_353
  | 4, _ => chunk_354
  | 5, _ => chunk_355
  | 6, _ => chunk_356
  | 7, _ => chunk_357
  | 8, _ => chunk_358
  | 9, _ => chunk_359
  | 10, _ => chunk_360
  | 11, _ => chunk_361
  | 12, _ => chunk_362
  | 13, _ => chunk_363
  | 14, _ => chunk_364
  | 15, _ => chunk_365
  | 16, _ => chunk_366
  | 17, _ => chunk_367
  | 18, _ => chunk_368
  | 19, _ => chunk_369
  | 20, _ => chunk_370
  | 21, _ => chunk_371
  | 22, _ => chunk_372
  | 23, _ => chunk_373
  | 24, _ => chunk_374
  | 25, _ => chunk_375
  | 26, _ => chunk_376
  | 27, _ => chunk_377
  | 28, _ => chunk_378
  | 29, _ => chunk_379
  | 30, _ => chunk_380
  | 31, _ => chunk_381
  | 32, _ => chunk_382
  | 33, _ => chunk_383
  | 34, _ => chunk_384
  | 35, _ => chunk_385
  | 36, _ => chunk_386
  | 37, _ => chunk_387
  | 38, _ => chunk_388
  | 39, _ => chunk_389
  | 40, _ => chunk_390
  | 41, _ => chunk_391
  | 42, _ => chunk_392
  | 43, _ => chunk_393
  | 44, _ => chunk_394
  | 45, _ => chunk_395
  | 46, _ => chunk_396
  | 47, _ => chunk_397
  | 48, _ => chunk_398
  | 49, _ => chunk_399
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
