import RSBounds.HelfgottSmall.Chunk.C0600
import RSBounds.HelfgottSmall.Chunk.C0601
import RSBounds.HelfgottSmall.Chunk.C0602
import RSBounds.HelfgottSmall.Chunk.C0603
import RSBounds.HelfgottSmall.Chunk.C0604
import RSBounds.HelfgottSmall.Chunk.C0605
import RSBounds.HelfgottSmall.Chunk.C0606
import RSBounds.HelfgottSmall.Chunk.C0607
import RSBounds.HelfgottSmall.Chunk.C0608
import RSBounds.HelfgottSmall.Chunk.C0609
import RSBounds.HelfgottSmall.Chunk.C0610
import RSBounds.HelfgottSmall.Chunk.C0611
import RSBounds.HelfgottSmall.Chunk.C0612
import RSBounds.HelfgottSmall.Chunk.C0613
import RSBounds.HelfgottSmall.Chunk.C0614
import RSBounds.HelfgottSmall.Chunk.C0615
import RSBounds.HelfgottSmall.Chunk.C0616
import RSBounds.HelfgottSmall.Chunk.C0617
import RSBounds.HelfgottSmall.Chunk.C0618
import RSBounds.HelfgottSmall.Chunk.C0619
import RSBounds.HelfgottSmall.Chunk.C0620
import RSBounds.HelfgottSmall.Chunk.C0621
import RSBounds.HelfgottSmall.Chunk.C0622
import RSBounds.HelfgottSmall.Chunk.C0623
import RSBounds.HelfgottSmall.Chunk.C0624
import RSBounds.HelfgottSmall.Chunk.C0625
import RSBounds.HelfgottSmall.Chunk.C0626
import RSBounds.HelfgottSmall.Chunk.C0627
import RSBounds.HelfgottSmall.Chunk.C0628
import RSBounds.HelfgottSmall.Chunk.C0629
import RSBounds.HelfgottSmall.Chunk.C0630
import RSBounds.HelfgottSmall.Chunk.C0631
import RSBounds.HelfgottSmall.Chunk.C0632
import RSBounds.HelfgottSmall.Chunk.C0633
import RSBounds.HelfgottSmall.Chunk.C0634
import RSBounds.HelfgottSmall.Chunk.C0635
import RSBounds.HelfgottSmall.Chunk.C0636
import RSBounds.HelfgottSmall.Chunk.C0637
import RSBounds.HelfgottSmall.Chunk.C0638
import RSBounds.HelfgottSmall.Chunk.C0639
import RSBounds.HelfgottSmall.Chunk.C0640
import RSBounds.HelfgottSmall.Chunk.C0641
import RSBounds.HelfgottSmall.Chunk.C0642
import RSBounds.HelfgottSmall.Chunk.C0643
import RSBounds.HelfgottSmall.Chunk.C0644
import RSBounds.HelfgottSmall.Chunk.C0645
import RSBounds.HelfgottSmall.Chunk.C0646
import RSBounds.HelfgottSmall.Chunk.C0647
import RSBounds.HelfgottSmall.Chunk.C0648
import RSBounds.HelfgottSmall.Chunk.C0649

/-! Walk chunks 600 to 649. -/

namespace RSBounds.HelfgottSmall

theorem group_12 (t : Nat) (ht : t < 50) : ChunkGood (600 + t) :=
  match t, ht with
  | 0, _ => chunk_600
  | 1, _ => chunk_601
  | 2, _ => chunk_602
  | 3, _ => chunk_603
  | 4, _ => chunk_604
  | 5, _ => chunk_605
  | 6, _ => chunk_606
  | 7, _ => chunk_607
  | 8, _ => chunk_608
  | 9, _ => chunk_609
  | 10, _ => chunk_610
  | 11, _ => chunk_611
  | 12, _ => chunk_612
  | 13, _ => chunk_613
  | 14, _ => chunk_614
  | 15, _ => chunk_615
  | 16, _ => chunk_616
  | 17, _ => chunk_617
  | 18, _ => chunk_618
  | 19, _ => chunk_619
  | 20, _ => chunk_620
  | 21, _ => chunk_621
  | 22, _ => chunk_622
  | 23, _ => chunk_623
  | 24, _ => chunk_624
  | 25, _ => chunk_625
  | 26, _ => chunk_626
  | 27, _ => chunk_627
  | 28, _ => chunk_628
  | 29, _ => chunk_629
  | 30, _ => chunk_630
  | 31, _ => chunk_631
  | 32, _ => chunk_632
  | 33, _ => chunk_633
  | 34, _ => chunk_634
  | 35, _ => chunk_635
  | 36, _ => chunk_636
  | 37, _ => chunk_637
  | 38, _ => chunk_638
  | 39, _ => chunk_639
  | 40, _ => chunk_640
  | 41, _ => chunk_641
  | 42, _ => chunk_642
  | 43, _ => chunk_643
  | 44, _ => chunk_644
  | 45, _ => chunk_645
  | 46, _ => chunk_646
  | 47, _ => chunk_647
  | 48, _ => chunk_648
  | 49, _ => chunk_649
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
