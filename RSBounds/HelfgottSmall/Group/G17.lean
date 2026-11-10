import RSBounds.HelfgottSmall.Chunk.C0850
import RSBounds.HelfgottSmall.Chunk.C0851
import RSBounds.HelfgottSmall.Chunk.C0852
import RSBounds.HelfgottSmall.Chunk.C0853
import RSBounds.HelfgottSmall.Chunk.C0854
import RSBounds.HelfgottSmall.Chunk.C0855
import RSBounds.HelfgottSmall.Chunk.C0856
import RSBounds.HelfgottSmall.Chunk.C0857
import RSBounds.HelfgottSmall.Chunk.C0858
import RSBounds.HelfgottSmall.Chunk.C0859
import RSBounds.HelfgottSmall.Chunk.C0860
import RSBounds.HelfgottSmall.Chunk.C0861
import RSBounds.HelfgottSmall.Chunk.C0862
import RSBounds.HelfgottSmall.Chunk.C0863
import RSBounds.HelfgottSmall.Chunk.C0864
import RSBounds.HelfgottSmall.Chunk.C0865
import RSBounds.HelfgottSmall.Chunk.C0866
import RSBounds.HelfgottSmall.Chunk.C0867
import RSBounds.HelfgottSmall.Chunk.C0868
import RSBounds.HelfgottSmall.Chunk.C0869
import RSBounds.HelfgottSmall.Chunk.C0870
import RSBounds.HelfgottSmall.Chunk.C0871
import RSBounds.HelfgottSmall.Chunk.C0872
import RSBounds.HelfgottSmall.Chunk.C0873
import RSBounds.HelfgottSmall.Chunk.C0874
import RSBounds.HelfgottSmall.Chunk.C0875
import RSBounds.HelfgottSmall.Chunk.C0876
import RSBounds.HelfgottSmall.Chunk.C0877
import RSBounds.HelfgottSmall.Chunk.C0878
import RSBounds.HelfgottSmall.Chunk.C0879
import RSBounds.HelfgottSmall.Chunk.C0880
import RSBounds.HelfgottSmall.Chunk.C0881
import RSBounds.HelfgottSmall.Chunk.C0882
import RSBounds.HelfgottSmall.Chunk.C0883
import RSBounds.HelfgottSmall.Chunk.C0884
import RSBounds.HelfgottSmall.Chunk.C0885
import RSBounds.HelfgottSmall.Chunk.C0886
import RSBounds.HelfgottSmall.Chunk.C0887
import RSBounds.HelfgottSmall.Chunk.C0888
import RSBounds.HelfgottSmall.Chunk.C0889
import RSBounds.HelfgottSmall.Chunk.C0890
import RSBounds.HelfgottSmall.Chunk.C0891
import RSBounds.HelfgottSmall.Chunk.C0892
import RSBounds.HelfgottSmall.Chunk.C0893
import RSBounds.HelfgottSmall.Chunk.C0894
import RSBounds.HelfgottSmall.Chunk.C0895
import RSBounds.HelfgottSmall.Chunk.C0896
import RSBounds.HelfgottSmall.Chunk.C0897
import RSBounds.HelfgottSmall.Chunk.C0898
import RSBounds.HelfgottSmall.Chunk.C0899

/-! Walk chunks 850 to 899. -/

namespace RSBounds.HelfgottSmall

theorem group_17 (t : Nat) (ht : t < 50) : ChunkGood (850 + t) :=
  match t, ht with
  | 0, _ => chunk_850
  | 1, _ => chunk_851
  | 2, _ => chunk_852
  | 3, _ => chunk_853
  | 4, _ => chunk_854
  | 5, _ => chunk_855
  | 6, _ => chunk_856
  | 7, _ => chunk_857
  | 8, _ => chunk_858
  | 9, _ => chunk_859
  | 10, _ => chunk_860
  | 11, _ => chunk_861
  | 12, _ => chunk_862
  | 13, _ => chunk_863
  | 14, _ => chunk_864
  | 15, _ => chunk_865
  | 16, _ => chunk_866
  | 17, _ => chunk_867
  | 18, _ => chunk_868
  | 19, _ => chunk_869
  | 20, _ => chunk_870
  | 21, _ => chunk_871
  | 22, _ => chunk_872
  | 23, _ => chunk_873
  | 24, _ => chunk_874
  | 25, _ => chunk_875
  | 26, _ => chunk_876
  | 27, _ => chunk_877
  | 28, _ => chunk_878
  | 29, _ => chunk_879
  | 30, _ => chunk_880
  | 31, _ => chunk_881
  | 32, _ => chunk_882
  | 33, _ => chunk_883
  | 34, _ => chunk_884
  | 35, _ => chunk_885
  | 36, _ => chunk_886
  | 37, _ => chunk_887
  | 38, _ => chunk_888
  | 39, _ => chunk_889
  | 40, _ => chunk_890
  | 41, _ => chunk_891
  | 42, _ => chunk_892
  | 43, _ => chunk_893
  | 44, _ => chunk_894
  | 45, _ => chunk_895
  | 46, _ => chunk_896
  | 47, _ => chunk_897
  | 48, _ => chunk_898
  | 49, _ => chunk_899
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
