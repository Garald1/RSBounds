import RSBounds.HelfgottSmall.Chunk.C0750
import RSBounds.HelfgottSmall.Chunk.C0751
import RSBounds.HelfgottSmall.Chunk.C0752
import RSBounds.HelfgottSmall.Chunk.C0753
import RSBounds.HelfgottSmall.Chunk.C0754
import RSBounds.HelfgottSmall.Chunk.C0755
import RSBounds.HelfgottSmall.Chunk.C0756
import RSBounds.HelfgottSmall.Chunk.C0757
import RSBounds.HelfgottSmall.Chunk.C0758
import RSBounds.HelfgottSmall.Chunk.C0759
import RSBounds.HelfgottSmall.Chunk.C0760
import RSBounds.HelfgottSmall.Chunk.C0761
import RSBounds.HelfgottSmall.Chunk.C0762
import RSBounds.HelfgottSmall.Chunk.C0763
import RSBounds.HelfgottSmall.Chunk.C0764
import RSBounds.HelfgottSmall.Chunk.C0765
import RSBounds.HelfgottSmall.Chunk.C0766
import RSBounds.HelfgottSmall.Chunk.C0767
import RSBounds.HelfgottSmall.Chunk.C0768
import RSBounds.HelfgottSmall.Chunk.C0769
import RSBounds.HelfgottSmall.Chunk.C0770
import RSBounds.HelfgottSmall.Chunk.C0771
import RSBounds.HelfgottSmall.Chunk.C0772
import RSBounds.HelfgottSmall.Chunk.C0773
import RSBounds.HelfgottSmall.Chunk.C0774
import RSBounds.HelfgottSmall.Chunk.C0775
import RSBounds.HelfgottSmall.Chunk.C0776
import RSBounds.HelfgottSmall.Chunk.C0777
import RSBounds.HelfgottSmall.Chunk.C0778
import RSBounds.HelfgottSmall.Chunk.C0779
import RSBounds.HelfgottSmall.Chunk.C0780
import RSBounds.HelfgottSmall.Chunk.C0781
import RSBounds.HelfgottSmall.Chunk.C0782
import RSBounds.HelfgottSmall.Chunk.C0783
import RSBounds.HelfgottSmall.Chunk.C0784
import RSBounds.HelfgottSmall.Chunk.C0785
import RSBounds.HelfgottSmall.Chunk.C0786
import RSBounds.HelfgottSmall.Chunk.C0787
import RSBounds.HelfgottSmall.Chunk.C0788
import RSBounds.HelfgottSmall.Chunk.C0789
import RSBounds.HelfgottSmall.Chunk.C0790
import RSBounds.HelfgottSmall.Chunk.C0791
import RSBounds.HelfgottSmall.Chunk.C0792
import RSBounds.HelfgottSmall.Chunk.C0793
import RSBounds.HelfgottSmall.Chunk.C0794
import RSBounds.HelfgottSmall.Chunk.C0795
import RSBounds.HelfgottSmall.Chunk.C0796
import RSBounds.HelfgottSmall.Chunk.C0797
import RSBounds.HelfgottSmall.Chunk.C0798
import RSBounds.HelfgottSmall.Chunk.C0799

/-! Walk chunks 750 to 799. -/

namespace RSBounds.HelfgottSmall

theorem group_15 (t : Nat) (ht : t < 50) : ChunkGood (750 + t) :=
  match t, ht with
  | 0, _ => chunk_750
  | 1, _ => chunk_751
  | 2, _ => chunk_752
  | 3, _ => chunk_753
  | 4, _ => chunk_754
  | 5, _ => chunk_755
  | 6, _ => chunk_756
  | 7, _ => chunk_757
  | 8, _ => chunk_758
  | 9, _ => chunk_759
  | 10, _ => chunk_760
  | 11, _ => chunk_761
  | 12, _ => chunk_762
  | 13, _ => chunk_763
  | 14, _ => chunk_764
  | 15, _ => chunk_765
  | 16, _ => chunk_766
  | 17, _ => chunk_767
  | 18, _ => chunk_768
  | 19, _ => chunk_769
  | 20, _ => chunk_770
  | 21, _ => chunk_771
  | 22, _ => chunk_772
  | 23, _ => chunk_773
  | 24, _ => chunk_774
  | 25, _ => chunk_775
  | 26, _ => chunk_776
  | 27, _ => chunk_777
  | 28, _ => chunk_778
  | 29, _ => chunk_779
  | 30, _ => chunk_780
  | 31, _ => chunk_781
  | 32, _ => chunk_782
  | 33, _ => chunk_783
  | 34, _ => chunk_784
  | 35, _ => chunk_785
  | 36, _ => chunk_786
  | 37, _ => chunk_787
  | 38, _ => chunk_788
  | 39, _ => chunk_789
  | 40, _ => chunk_790
  | 41, _ => chunk_791
  | 42, _ => chunk_792
  | 43, _ => chunk_793
  | 44, _ => chunk_794
  | 45, _ => chunk_795
  | 46, _ => chunk_796
  | 47, _ => chunk_797
  | 48, _ => chunk_798
  | 49, _ => chunk_799
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
