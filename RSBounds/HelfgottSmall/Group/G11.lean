import RSBounds.HelfgottSmall.Chunk.C0550
import RSBounds.HelfgottSmall.Chunk.C0551
import RSBounds.HelfgottSmall.Chunk.C0552
import RSBounds.HelfgottSmall.Chunk.C0553
import RSBounds.HelfgottSmall.Chunk.C0554
import RSBounds.HelfgottSmall.Chunk.C0555
import RSBounds.HelfgottSmall.Chunk.C0556
import RSBounds.HelfgottSmall.Chunk.C0557
import RSBounds.HelfgottSmall.Chunk.C0558
import RSBounds.HelfgottSmall.Chunk.C0559
import RSBounds.HelfgottSmall.Chunk.C0560
import RSBounds.HelfgottSmall.Chunk.C0561
import RSBounds.HelfgottSmall.Chunk.C0562
import RSBounds.HelfgottSmall.Chunk.C0563
import RSBounds.HelfgottSmall.Chunk.C0564
import RSBounds.HelfgottSmall.Chunk.C0565
import RSBounds.HelfgottSmall.Chunk.C0566
import RSBounds.HelfgottSmall.Chunk.C0567
import RSBounds.HelfgottSmall.Chunk.C0568
import RSBounds.HelfgottSmall.Chunk.C0569
import RSBounds.HelfgottSmall.Chunk.C0570
import RSBounds.HelfgottSmall.Chunk.C0571
import RSBounds.HelfgottSmall.Chunk.C0572
import RSBounds.HelfgottSmall.Chunk.C0573
import RSBounds.HelfgottSmall.Chunk.C0574
import RSBounds.HelfgottSmall.Chunk.C0575
import RSBounds.HelfgottSmall.Chunk.C0576
import RSBounds.HelfgottSmall.Chunk.C0577
import RSBounds.HelfgottSmall.Chunk.C0578
import RSBounds.HelfgottSmall.Chunk.C0579
import RSBounds.HelfgottSmall.Chunk.C0580
import RSBounds.HelfgottSmall.Chunk.C0581
import RSBounds.HelfgottSmall.Chunk.C0582
import RSBounds.HelfgottSmall.Chunk.C0583
import RSBounds.HelfgottSmall.Chunk.C0584
import RSBounds.HelfgottSmall.Chunk.C0585
import RSBounds.HelfgottSmall.Chunk.C0586
import RSBounds.HelfgottSmall.Chunk.C0587
import RSBounds.HelfgottSmall.Chunk.C0588
import RSBounds.HelfgottSmall.Chunk.C0589
import RSBounds.HelfgottSmall.Chunk.C0590
import RSBounds.HelfgottSmall.Chunk.C0591
import RSBounds.HelfgottSmall.Chunk.C0592
import RSBounds.HelfgottSmall.Chunk.C0593
import RSBounds.HelfgottSmall.Chunk.C0594
import RSBounds.HelfgottSmall.Chunk.C0595
import RSBounds.HelfgottSmall.Chunk.C0596
import RSBounds.HelfgottSmall.Chunk.C0597
import RSBounds.HelfgottSmall.Chunk.C0598
import RSBounds.HelfgottSmall.Chunk.C0599

/-! Walk chunks 550 to 599. -/

namespace RSBounds.HelfgottSmall

theorem group_11 (t : Nat) (ht : t < 50) : ChunkGood (550 + t) :=
  match t, ht with
  | 0, _ => chunk_550
  | 1, _ => chunk_551
  | 2, _ => chunk_552
  | 3, _ => chunk_553
  | 4, _ => chunk_554
  | 5, _ => chunk_555
  | 6, _ => chunk_556
  | 7, _ => chunk_557
  | 8, _ => chunk_558
  | 9, _ => chunk_559
  | 10, _ => chunk_560
  | 11, _ => chunk_561
  | 12, _ => chunk_562
  | 13, _ => chunk_563
  | 14, _ => chunk_564
  | 15, _ => chunk_565
  | 16, _ => chunk_566
  | 17, _ => chunk_567
  | 18, _ => chunk_568
  | 19, _ => chunk_569
  | 20, _ => chunk_570
  | 21, _ => chunk_571
  | 22, _ => chunk_572
  | 23, _ => chunk_573
  | 24, _ => chunk_574
  | 25, _ => chunk_575
  | 26, _ => chunk_576
  | 27, _ => chunk_577
  | 28, _ => chunk_578
  | 29, _ => chunk_579
  | 30, _ => chunk_580
  | 31, _ => chunk_581
  | 32, _ => chunk_582
  | 33, _ => chunk_583
  | 34, _ => chunk_584
  | 35, _ => chunk_585
  | 36, _ => chunk_586
  | 37, _ => chunk_587
  | 38, _ => chunk_588
  | 39, _ => chunk_589
  | 40, _ => chunk_590
  | 41, _ => chunk_591
  | 42, _ => chunk_592
  | 43, _ => chunk_593
  | 44, _ => chunk_594
  | 45, _ => chunk_595
  | 46, _ => chunk_596
  | 47, _ => chunk_597
  | 48, _ => chunk_598
  | 49, _ => chunk_599
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
