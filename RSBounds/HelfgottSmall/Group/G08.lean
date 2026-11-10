import RSBounds.HelfgottSmall.Chunk.C0400
import RSBounds.HelfgottSmall.Chunk.C0401
import RSBounds.HelfgottSmall.Chunk.C0402
import RSBounds.HelfgottSmall.Chunk.C0403
import RSBounds.HelfgottSmall.Chunk.C0404
import RSBounds.HelfgottSmall.Chunk.C0405
import RSBounds.HelfgottSmall.Chunk.C0406
import RSBounds.HelfgottSmall.Chunk.C0407
import RSBounds.HelfgottSmall.Chunk.C0408
import RSBounds.HelfgottSmall.Chunk.C0409
import RSBounds.HelfgottSmall.Chunk.C0410
import RSBounds.HelfgottSmall.Chunk.C0411
import RSBounds.HelfgottSmall.Chunk.C0412
import RSBounds.HelfgottSmall.Chunk.C0413
import RSBounds.HelfgottSmall.Chunk.C0414
import RSBounds.HelfgottSmall.Chunk.C0415
import RSBounds.HelfgottSmall.Chunk.C0416
import RSBounds.HelfgottSmall.Chunk.C0417
import RSBounds.HelfgottSmall.Chunk.C0418
import RSBounds.HelfgottSmall.Chunk.C0419
import RSBounds.HelfgottSmall.Chunk.C0420
import RSBounds.HelfgottSmall.Chunk.C0421
import RSBounds.HelfgottSmall.Chunk.C0422
import RSBounds.HelfgottSmall.Chunk.C0423
import RSBounds.HelfgottSmall.Chunk.C0424
import RSBounds.HelfgottSmall.Chunk.C0425
import RSBounds.HelfgottSmall.Chunk.C0426
import RSBounds.HelfgottSmall.Chunk.C0427
import RSBounds.HelfgottSmall.Chunk.C0428
import RSBounds.HelfgottSmall.Chunk.C0429
import RSBounds.HelfgottSmall.Chunk.C0430
import RSBounds.HelfgottSmall.Chunk.C0431
import RSBounds.HelfgottSmall.Chunk.C0432
import RSBounds.HelfgottSmall.Chunk.C0433
import RSBounds.HelfgottSmall.Chunk.C0434
import RSBounds.HelfgottSmall.Chunk.C0435
import RSBounds.HelfgottSmall.Chunk.C0436
import RSBounds.HelfgottSmall.Chunk.C0437
import RSBounds.HelfgottSmall.Chunk.C0438
import RSBounds.HelfgottSmall.Chunk.C0439
import RSBounds.HelfgottSmall.Chunk.C0440
import RSBounds.HelfgottSmall.Chunk.C0441
import RSBounds.HelfgottSmall.Chunk.C0442
import RSBounds.HelfgottSmall.Chunk.C0443
import RSBounds.HelfgottSmall.Chunk.C0444
import RSBounds.HelfgottSmall.Chunk.C0445
import RSBounds.HelfgottSmall.Chunk.C0446
import RSBounds.HelfgottSmall.Chunk.C0447
import RSBounds.HelfgottSmall.Chunk.C0448
import RSBounds.HelfgottSmall.Chunk.C0449

/-! Walk chunks 400 to 449. -/

namespace RSBounds.HelfgottSmall

theorem group_8 (t : Nat) (ht : t < 50) : ChunkGood (400 + t) :=
  match t, ht with
  | 0, _ => chunk_400
  | 1, _ => chunk_401
  | 2, _ => chunk_402
  | 3, _ => chunk_403
  | 4, _ => chunk_404
  | 5, _ => chunk_405
  | 6, _ => chunk_406
  | 7, _ => chunk_407
  | 8, _ => chunk_408
  | 9, _ => chunk_409
  | 10, _ => chunk_410
  | 11, _ => chunk_411
  | 12, _ => chunk_412
  | 13, _ => chunk_413
  | 14, _ => chunk_414
  | 15, _ => chunk_415
  | 16, _ => chunk_416
  | 17, _ => chunk_417
  | 18, _ => chunk_418
  | 19, _ => chunk_419
  | 20, _ => chunk_420
  | 21, _ => chunk_421
  | 22, _ => chunk_422
  | 23, _ => chunk_423
  | 24, _ => chunk_424
  | 25, _ => chunk_425
  | 26, _ => chunk_426
  | 27, _ => chunk_427
  | 28, _ => chunk_428
  | 29, _ => chunk_429
  | 30, _ => chunk_430
  | 31, _ => chunk_431
  | 32, _ => chunk_432
  | 33, _ => chunk_433
  | 34, _ => chunk_434
  | 35, _ => chunk_435
  | 36, _ => chunk_436
  | 37, _ => chunk_437
  | 38, _ => chunk_438
  | 39, _ => chunk_439
  | 40, _ => chunk_440
  | 41, _ => chunk_441
  | 42, _ => chunk_442
  | 43, _ => chunk_443
  | 44, _ => chunk_444
  | 45, _ => chunk_445
  | 46, _ => chunk_446
  | 47, _ => chunk_447
  | 48, _ => chunk_448
  | 49, _ => chunk_449
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
