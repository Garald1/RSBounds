import RSBounds.HelfgottSmall.Chunk.C0900
import RSBounds.HelfgottSmall.Chunk.C0901
import RSBounds.HelfgottSmall.Chunk.C0902
import RSBounds.HelfgottSmall.Chunk.C0903
import RSBounds.HelfgottSmall.Chunk.C0904
import RSBounds.HelfgottSmall.Chunk.C0905
import RSBounds.HelfgottSmall.Chunk.C0906
import RSBounds.HelfgottSmall.Chunk.C0907
import RSBounds.HelfgottSmall.Chunk.C0908
import RSBounds.HelfgottSmall.Chunk.C0909
import RSBounds.HelfgottSmall.Chunk.C0910
import RSBounds.HelfgottSmall.Chunk.C0911
import RSBounds.HelfgottSmall.Chunk.C0912
import RSBounds.HelfgottSmall.Chunk.C0913
import RSBounds.HelfgottSmall.Chunk.C0914
import RSBounds.HelfgottSmall.Chunk.C0915
import RSBounds.HelfgottSmall.Chunk.C0916
import RSBounds.HelfgottSmall.Chunk.C0917
import RSBounds.HelfgottSmall.Chunk.C0918
import RSBounds.HelfgottSmall.Chunk.C0919
import RSBounds.HelfgottSmall.Chunk.C0920
import RSBounds.HelfgottSmall.Chunk.C0921
import RSBounds.HelfgottSmall.Chunk.C0922
import RSBounds.HelfgottSmall.Chunk.C0923
import RSBounds.HelfgottSmall.Chunk.C0924
import RSBounds.HelfgottSmall.Chunk.C0925
import RSBounds.HelfgottSmall.Chunk.C0926
import RSBounds.HelfgottSmall.Chunk.C0927
import RSBounds.HelfgottSmall.Chunk.C0928
import RSBounds.HelfgottSmall.Chunk.C0929
import RSBounds.HelfgottSmall.Chunk.C0930
import RSBounds.HelfgottSmall.Chunk.C0931
import RSBounds.HelfgottSmall.Chunk.C0932
import RSBounds.HelfgottSmall.Chunk.C0933
import RSBounds.HelfgottSmall.Chunk.C0934
import RSBounds.HelfgottSmall.Chunk.C0935
import RSBounds.HelfgottSmall.Chunk.C0936
import RSBounds.HelfgottSmall.Chunk.C0937
import RSBounds.HelfgottSmall.Chunk.C0938
import RSBounds.HelfgottSmall.Chunk.C0939
import RSBounds.HelfgottSmall.Chunk.C0940
import RSBounds.HelfgottSmall.Chunk.C0941
import RSBounds.HelfgottSmall.Chunk.C0942
import RSBounds.HelfgottSmall.Chunk.C0943
import RSBounds.HelfgottSmall.Chunk.C0944
import RSBounds.HelfgottSmall.Chunk.C0945
import RSBounds.HelfgottSmall.Chunk.C0946
import RSBounds.HelfgottSmall.Chunk.C0947
import RSBounds.HelfgottSmall.Chunk.C0948
import RSBounds.HelfgottSmall.Chunk.C0949

/-! Walk chunks 900 to 949. -/

namespace RSBounds.HelfgottSmall

theorem group_18 (t : Nat) (ht : t < 50) : ChunkGood (900 + t) :=
  match t, ht with
  | 0, _ => chunk_900
  | 1, _ => chunk_901
  | 2, _ => chunk_902
  | 3, _ => chunk_903
  | 4, _ => chunk_904
  | 5, _ => chunk_905
  | 6, _ => chunk_906
  | 7, _ => chunk_907
  | 8, _ => chunk_908
  | 9, _ => chunk_909
  | 10, _ => chunk_910
  | 11, _ => chunk_911
  | 12, _ => chunk_912
  | 13, _ => chunk_913
  | 14, _ => chunk_914
  | 15, _ => chunk_915
  | 16, _ => chunk_916
  | 17, _ => chunk_917
  | 18, _ => chunk_918
  | 19, _ => chunk_919
  | 20, _ => chunk_920
  | 21, _ => chunk_921
  | 22, _ => chunk_922
  | 23, _ => chunk_923
  | 24, _ => chunk_924
  | 25, _ => chunk_925
  | 26, _ => chunk_926
  | 27, _ => chunk_927
  | 28, _ => chunk_928
  | 29, _ => chunk_929
  | 30, _ => chunk_930
  | 31, _ => chunk_931
  | 32, _ => chunk_932
  | 33, _ => chunk_933
  | 34, _ => chunk_934
  | 35, _ => chunk_935
  | 36, _ => chunk_936
  | 37, _ => chunk_937
  | 38, _ => chunk_938
  | 39, _ => chunk_939
  | 40, _ => chunk_940
  | 41, _ => chunk_941
  | 42, _ => chunk_942
  | 43, _ => chunk_943
  | 44, _ => chunk_944
  | 45, _ => chunk_945
  | 46, _ => chunk_946
  | 47, _ => chunk_947
  | 48, _ => chunk_948
  | 49, _ => chunk_949
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
