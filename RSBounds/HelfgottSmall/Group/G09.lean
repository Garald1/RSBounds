import RSBounds.HelfgottSmall.Chunk.C0450
import RSBounds.HelfgottSmall.Chunk.C0451
import RSBounds.HelfgottSmall.Chunk.C0452
import RSBounds.HelfgottSmall.Chunk.C0453
import RSBounds.HelfgottSmall.Chunk.C0454
import RSBounds.HelfgottSmall.Chunk.C0455
import RSBounds.HelfgottSmall.Chunk.C0456
import RSBounds.HelfgottSmall.Chunk.C0457
import RSBounds.HelfgottSmall.Chunk.C0458
import RSBounds.HelfgottSmall.Chunk.C0459
import RSBounds.HelfgottSmall.Chunk.C0460
import RSBounds.HelfgottSmall.Chunk.C0461
import RSBounds.HelfgottSmall.Chunk.C0462
import RSBounds.HelfgottSmall.Chunk.C0463
import RSBounds.HelfgottSmall.Chunk.C0464
import RSBounds.HelfgottSmall.Chunk.C0465
import RSBounds.HelfgottSmall.Chunk.C0466
import RSBounds.HelfgottSmall.Chunk.C0467
import RSBounds.HelfgottSmall.Chunk.C0468
import RSBounds.HelfgottSmall.Chunk.C0469
import RSBounds.HelfgottSmall.Chunk.C0470
import RSBounds.HelfgottSmall.Chunk.C0471
import RSBounds.HelfgottSmall.Chunk.C0472
import RSBounds.HelfgottSmall.Chunk.C0473
import RSBounds.HelfgottSmall.Chunk.C0474
import RSBounds.HelfgottSmall.Chunk.C0475
import RSBounds.HelfgottSmall.Chunk.C0476
import RSBounds.HelfgottSmall.Chunk.C0477
import RSBounds.HelfgottSmall.Chunk.C0478
import RSBounds.HelfgottSmall.Chunk.C0479
import RSBounds.HelfgottSmall.Chunk.C0480
import RSBounds.HelfgottSmall.Chunk.C0481
import RSBounds.HelfgottSmall.Chunk.C0482
import RSBounds.HelfgottSmall.Chunk.C0483
import RSBounds.HelfgottSmall.Chunk.C0484
import RSBounds.HelfgottSmall.Chunk.C0485
import RSBounds.HelfgottSmall.Chunk.C0486
import RSBounds.HelfgottSmall.Chunk.C0487
import RSBounds.HelfgottSmall.Chunk.C0488
import RSBounds.HelfgottSmall.Chunk.C0489
import RSBounds.HelfgottSmall.Chunk.C0490
import RSBounds.HelfgottSmall.Chunk.C0491
import RSBounds.HelfgottSmall.Chunk.C0492
import RSBounds.HelfgottSmall.Chunk.C0493
import RSBounds.HelfgottSmall.Chunk.C0494
import RSBounds.HelfgottSmall.Chunk.C0495
import RSBounds.HelfgottSmall.Chunk.C0496
import RSBounds.HelfgottSmall.Chunk.C0497
import RSBounds.HelfgottSmall.Chunk.C0498
import RSBounds.HelfgottSmall.Chunk.C0499

/-! Walk chunks 450 to 499. -/

namespace RSBounds.HelfgottSmall

theorem group_9 (t : Nat) (ht : t < 50) : ChunkGood (450 + t) :=
  match t, ht with
  | 0, _ => chunk_450
  | 1, _ => chunk_451
  | 2, _ => chunk_452
  | 3, _ => chunk_453
  | 4, _ => chunk_454
  | 5, _ => chunk_455
  | 6, _ => chunk_456
  | 7, _ => chunk_457
  | 8, _ => chunk_458
  | 9, _ => chunk_459
  | 10, _ => chunk_460
  | 11, _ => chunk_461
  | 12, _ => chunk_462
  | 13, _ => chunk_463
  | 14, _ => chunk_464
  | 15, _ => chunk_465
  | 16, _ => chunk_466
  | 17, _ => chunk_467
  | 18, _ => chunk_468
  | 19, _ => chunk_469
  | 20, _ => chunk_470
  | 21, _ => chunk_471
  | 22, _ => chunk_472
  | 23, _ => chunk_473
  | 24, _ => chunk_474
  | 25, _ => chunk_475
  | 26, _ => chunk_476
  | 27, _ => chunk_477
  | 28, _ => chunk_478
  | 29, _ => chunk_479
  | 30, _ => chunk_480
  | 31, _ => chunk_481
  | 32, _ => chunk_482
  | 33, _ => chunk_483
  | 34, _ => chunk_484
  | 35, _ => chunk_485
  | 36, _ => chunk_486
  | 37, _ => chunk_487
  | 38, _ => chunk_488
  | 39, _ => chunk_489
  | 40, _ => chunk_490
  | 41, _ => chunk_491
  | 42, _ => chunk_492
  | 43, _ => chunk_493
  | 44, _ => chunk_494
  | 45, _ => chunk_495
  | 46, _ => chunk_496
  | 47, _ => chunk_497
  | 48, _ => chunk_498
  | 49, _ => chunk_499
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
