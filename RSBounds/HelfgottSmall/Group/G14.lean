import RSBounds.HelfgottSmall.Chunk.C0700
import RSBounds.HelfgottSmall.Chunk.C0701
import RSBounds.HelfgottSmall.Chunk.C0702
import RSBounds.HelfgottSmall.Chunk.C0703
import RSBounds.HelfgottSmall.Chunk.C0704
import RSBounds.HelfgottSmall.Chunk.C0705
import RSBounds.HelfgottSmall.Chunk.C0706
import RSBounds.HelfgottSmall.Chunk.C0707
import RSBounds.HelfgottSmall.Chunk.C0708
import RSBounds.HelfgottSmall.Chunk.C0709
import RSBounds.HelfgottSmall.Chunk.C0710
import RSBounds.HelfgottSmall.Chunk.C0711
import RSBounds.HelfgottSmall.Chunk.C0712
import RSBounds.HelfgottSmall.Chunk.C0713
import RSBounds.HelfgottSmall.Chunk.C0714
import RSBounds.HelfgottSmall.Chunk.C0715
import RSBounds.HelfgottSmall.Chunk.C0716
import RSBounds.HelfgottSmall.Chunk.C0717
import RSBounds.HelfgottSmall.Chunk.C0718
import RSBounds.HelfgottSmall.Chunk.C0719
import RSBounds.HelfgottSmall.Chunk.C0720
import RSBounds.HelfgottSmall.Chunk.C0721
import RSBounds.HelfgottSmall.Chunk.C0722
import RSBounds.HelfgottSmall.Chunk.C0723
import RSBounds.HelfgottSmall.Chunk.C0724
import RSBounds.HelfgottSmall.Chunk.C0725
import RSBounds.HelfgottSmall.Chunk.C0726
import RSBounds.HelfgottSmall.Chunk.C0727
import RSBounds.HelfgottSmall.Chunk.C0728
import RSBounds.HelfgottSmall.Chunk.C0729
import RSBounds.HelfgottSmall.Chunk.C0730
import RSBounds.HelfgottSmall.Chunk.C0731
import RSBounds.HelfgottSmall.Chunk.C0732
import RSBounds.HelfgottSmall.Chunk.C0733
import RSBounds.HelfgottSmall.Chunk.C0734
import RSBounds.HelfgottSmall.Chunk.C0735
import RSBounds.HelfgottSmall.Chunk.C0736
import RSBounds.HelfgottSmall.Chunk.C0737
import RSBounds.HelfgottSmall.Chunk.C0738
import RSBounds.HelfgottSmall.Chunk.C0739
import RSBounds.HelfgottSmall.Chunk.C0740
import RSBounds.HelfgottSmall.Chunk.C0741
import RSBounds.HelfgottSmall.Chunk.C0742
import RSBounds.HelfgottSmall.Chunk.C0743
import RSBounds.HelfgottSmall.Chunk.C0744
import RSBounds.HelfgottSmall.Chunk.C0745
import RSBounds.HelfgottSmall.Chunk.C0746
import RSBounds.HelfgottSmall.Chunk.C0747
import RSBounds.HelfgottSmall.Chunk.C0748
import RSBounds.HelfgottSmall.Chunk.C0749

/-! Walk chunks 700 to 749. -/

namespace RSBounds.HelfgottSmall

theorem group_14 (t : Nat) (ht : t < 50) : ChunkGood (700 + t) :=
  match t, ht with
  | 0, _ => chunk_700
  | 1, _ => chunk_701
  | 2, _ => chunk_702
  | 3, _ => chunk_703
  | 4, _ => chunk_704
  | 5, _ => chunk_705
  | 6, _ => chunk_706
  | 7, _ => chunk_707
  | 8, _ => chunk_708
  | 9, _ => chunk_709
  | 10, _ => chunk_710
  | 11, _ => chunk_711
  | 12, _ => chunk_712
  | 13, _ => chunk_713
  | 14, _ => chunk_714
  | 15, _ => chunk_715
  | 16, _ => chunk_716
  | 17, _ => chunk_717
  | 18, _ => chunk_718
  | 19, _ => chunk_719
  | 20, _ => chunk_720
  | 21, _ => chunk_721
  | 22, _ => chunk_722
  | 23, _ => chunk_723
  | 24, _ => chunk_724
  | 25, _ => chunk_725
  | 26, _ => chunk_726
  | 27, _ => chunk_727
  | 28, _ => chunk_728
  | 29, _ => chunk_729
  | 30, _ => chunk_730
  | 31, _ => chunk_731
  | 32, _ => chunk_732
  | 33, _ => chunk_733
  | 34, _ => chunk_734
  | 35, _ => chunk_735
  | 36, _ => chunk_736
  | 37, _ => chunk_737
  | 38, _ => chunk_738
  | 39, _ => chunk_739
  | 40, _ => chunk_740
  | 41, _ => chunk_741
  | 42, _ => chunk_742
  | 43, _ => chunk_743
  | 44, _ => chunk_744
  | 45, _ => chunk_745
  | 46, _ => chunk_746
  | 47, _ => chunk_747
  | 48, _ => chunk_748
  | 49, _ => chunk_749
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
