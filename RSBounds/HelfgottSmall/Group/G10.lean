import RSBounds.HelfgottSmall.Chunk.C0500
import RSBounds.HelfgottSmall.Chunk.C0501
import RSBounds.HelfgottSmall.Chunk.C0502
import RSBounds.HelfgottSmall.Chunk.C0503
import RSBounds.HelfgottSmall.Chunk.C0504
import RSBounds.HelfgottSmall.Chunk.C0505
import RSBounds.HelfgottSmall.Chunk.C0506
import RSBounds.HelfgottSmall.Chunk.C0507
import RSBounds.HelfgottSmall.Chunk.C0508
import RSBounds.HelfgottSmall.Chunk.C0509
import RSBounds.HelfgottSmall.Chunk.C0510
import RSBounds.HelfgottSmall.Chunk.C0511
import RSBounds.HelfgottSmall.Chunk.C0512
import RSBounds.HelfgottSmall.Chunk.C0513
import RSBounds.HelfgottSmall.Chunk.C0514
import RSBounds.HelfgottSmall.Chunk.C0515
import RSBounds.HelfgottSmall.Chunk.C0516
import RSBounds.HelfgottSmall.Chunk.C0517
import RSBounds.HelfgottSmall.Chunk.C0518
import RSBounds.HelfgottSmall.Chunk.C0519
import RSBounds.HelfgottSmall.Chunk.C0520
import RSBounds.HelfgottSmall.Chunk.C0521
import RSBounds.HelfgottSmall.Chunk.C0522
import RSBounds.HelfgottSmall.Chunk.C0523
import RSBounds.HelfgottSmall.Chunk.C0524
import RSBounds.HelfgottSmall.Chunk.C0525
import RSBounds.HelfgottSmall.Chunk.C0526
import RSBounds.HelfgottSmall.Chunk.C0527
import RSBounds.HelfgottSmall.Chunk.C0528
import RSBounds.HelfgottSmall.Chunk.C0529
import RSBounds.HelfgottSmall.Chunk.C0530
import RSBounds.HelfgottSmall.Chunk.C0531
import RSBounds.HelfgottSmall.Chunk.C0532
import RSBounds.HelfgottSmall.Chunk.C0533
import RSBounds.HelfgottSmall.Chunk.C0534
import RSBounds.HelfgottSmall.Chunk.C0535
import RSBounds.HelfgottSmall.Chunk.C0536
import RSBounds.HelfgottSmall.Chunk.C0537
import RSBounds.HelfgottSmall.Chunk.C0538
import RSBounds.HelfgottSmall.Chunk.C0539
import RSBounds.HelfgottSmall.Chunk.C0540
import RSBounds.HelfgottSmall.Chunk.C0541
import RSBounds.HelfgottSmall.Chunk.C0542
import RSBounds.HelfgottSmall.Chunk.C0543
import RSBounds.HelfgottSmall.Chunk.C0544
import RSBounds.HelfgottSmall.Chunk.C0545
import RSBounds.HelfgottSmall.Chunk.C0546
import RSBounds.HelfgottSmall.Chunk.C0547
import RSBounds.HelfgottSmall.Chunk.C0548
import RSBounds.HelfgottSmall.Chunk.C0549

/-! Walk chunks 500 to 549. -/

namespace RSBounds.HelfgottSmall

theorem group_10 (t : Nat) (ht : t < 50) : ChunkGood (500 + t) :=
  match t, ht with
  | 0, _ => chunk_500
  | 1, _ => chunk_501
  | 2, _ => chunk_502
  | 3, _ => chunk_503
  | 4, _ => chunk_504
  | 5, _ => chunk_505
  | 6, _ => chunk_506
  | 7, _ => chunk_507
  | 8, _ => chunk_508
  | 9, _ => chunk_509
  | 10, _ => chunk_510
  | 11, _ => chunk_511
  | 12, _ => chunk_512
  | 13, _ => chunk_513
  | 14, _ => chunk_514
  | 15, _ => chunk_515
  | 16, _ => chunk_516
  | 17, _ => chunk_517
  | 18, _ => chunk_518
  | 19, _ => chunk_519
  | 20, _ => chunk_520
  | 21, _ => chunk_521
  | 22, _ => chunk_522
  | 23, _ => chunk_523
  | 24, _ => chunk_524
  | 25, _ => chunk_525
  | 26, _ => chunk_526
  | 27, _ => chunk_527
  | 28, _ => chunk_528
  | 29, _ => chunk_529
  | 30, _ => chunk_530
  | 31, _ => chunk_531
  | 32, _ => chunk_532
  | 33, _ => chunk_533
  | 34, _ => chunk_534
  | 35, _ => chunk_535
  | 36, _ => chunk_536
  | 37, _ => chunk_537
  | 38, _ => chunk_538
  | 39, _ => chunk_539
  | 40, _ => chunk_540
  | 41, _ => chunk_541
  | 42, _ => chunk_542
  | 43, _ => chunk_543
  | 44, _ => chunk_544
  | 45, _ => chunk_545
  | 46, _ => chunk_546
  | 47, _ => chunk_547
  | 48, _ => chunk_548
  | 49, _ => chunk_549
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
