import RSBounds.HelfgottSmall.Chunk.C0650
import RSBounds.HelfgottSmall.Chunk.C0651
import RSBounds.HelfgottSmall.Chunk.C0652
import RSBounds.HelfgottSmall.Chunk.C0653
import RSBounds.HelfgottSmall.Chunk.C0654
import RSBounds.HelfgottSmall.Chunk.C0655
import RSBounds.HelfgottSmall.Chunk.C0656
import RSBounds.HelfgottSmall.Chunk.C0657
import RSBounds.HelfgottSmall.Chunk.C0658
import RSBounds.HelfgottSmall.Chunk.C0659
import RSBounds.HelfgottSmall.Chunk.C0660
import RSBounds.HelfgottSmall.Chunk.C0661
import RSBounds.HelfgottSmall.Chunk.C0662
import RSBounds.HelfgottSmall.Chunk.C0663
import RSBounds.HelfgottSmall.Chunk.C0664
import RSBounds.HelfgottSmall.Chunk.C0665
import RSBounds.HelfgottSmall.Chunk.C0666
import RSBounds.HelfgottSmall.Chunk.C0667
import RSBounds.HelfgottSmall.Chunk.C0668
import RSBounds.HelfgottSmall.Chunk.C0669
import RSBounds.HelfgottSmall.Chunk.C0670
import RSBounds.HelfgottSmall.Chunk.C0671
import RSBounds.HelfgottSmall.Chunk.C0672
import RSBounds.HelfgottSmall.Chunk.C0673
import RSBounds.HelfgottSmall.Chunk.C0674
import RSBounds.HelfgottSmall.Chunk.C0675
import RSBounds.HelfgottSmall.Chunk.C0676
import RSBounds.HelfgottSmall.Chunk.C0677
import RSBounds.HelfgottSmall.Chunk.C0678
import RSBounds.HelfgottSmall.Chunk.C0679
import RSBounds.HelfgottSmall.Chunk.C0680
import RSBounds.HelfgottSmall.Chunk.C0681
import RSBounds.HelfgottSmall.Chunk.C0682
import RSBounds.HelfgottSmall.Chunk.C0683
import RSBounds.HelfgottSmall.Chunk.C0684
import RSBounds.HelfgottSmall.Chunk.C0685
import RSBounds.HelfgottSmall.Chunk.C0686
import RSBounds.HelfgottSmall.Chunk.C0687
import RSBounds.HelfgottSmall.Chunk.C0688
import RSBounds.HelfgottSmall.Chunk.C0689
import RSBounds.HelfgottSmall.Chunk.C0690
import RSBounds.HelfgottSmall.Chunk.C0691
import RSBounds.HelfgottSmall.Chunk.C0692
import RSBounds.HelfgottSmall.Chunk.C0693
import RSBounds.HelfgottSmall.Chunk.C0694
import RSBounds.HelfgottSmall.Chunk.C0695
import RSBounds.HelfgottSmall.Chunk.C0696
import RSBounds.HelfgottSmall.Chunk.C0697
import RSBounds.HelfgottSmall.Chunk.C0698
import RSBounds.HelfgottSmall.Chunk.C0699

/-! Walk chunks 650 to 699. -/

namespace RSBounds.HelfgottSmall

theorem group_13 (t : Nat) (ht : t < 50) : ChunkGood (650 + t) :=
  match t, ht with
  | 0, _ => chunk_650
  | 1, _ => chunk_651
  | 2, _ => chunk_652
  | 3, _ => chunk_653
  | 4, _ => chunk_654
  | 5, _ => chunk_655
  | 6, _ => chunk_656
  | 7, _ => chunk_657
  | 8, _ => chunk_658
  | 9, _ => chunk_659
  | 10, _ => chunk_660
  | 11, _ => chunk_661
  | 12, _ => chunk_662
  | 13, _ => chunk_663
  | 14, _ => chunk_664
  | 15, _ => chunk_665
  | 16, _ => chunk_666
  | 17, _ => chunk_667
  | 18, _ => chunk_668
  | 19, _ => chunk_669
  | 20, _ => chunk_670
  | 21, _ => chunk_671
  | 22, _ => chunk_672
  | 23, _ => chunk_673
  | 24, _ => chunk_674
  | 25, _ => chunk_675
  | 26, _ => chunk_676
  | 27, _ => chunk_677
  | 28, _ => chunk_678
  | 29, _ => chunk_679
  | 30, _ => chunk_680
  | 31, _ => chunk_681
  | 32, _ => chunk_682
  | 33, _ => chunk_683
  | 34, _ => chunk_684
  | 35, _ => chunk_685
  | 36, _ => chunk_686
  | 37, _ => chunk_687
  | 38, _ => chunk_688
  | 39, _ => chunk_689
  | 40, _ => chunk_690
  | 41, _ => chunk_691
  | 42, _ => chunk_692
  | 43, _ => chunk_693
  | 44, _ => chunk_694
  | 45, _ => chunk_695
  | 46, _ => chunk_696
  | 47, _ => chunk_697
  | 48, _ => chunk_698
  | 49, _ => chunk_699
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
