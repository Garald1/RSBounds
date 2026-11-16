import RSBounds.HelfgottSmall.Chunk.C0950
import RSBounds.HelfgottSmall.Chunk.C0951
import RSBounds.HelfgottSmall.Chunk.C0952
import RSBounds.HelfgottSmall.Chunk.C0953
import RSBounds.HelfgottSmall.Chunk.C0954
import RSBounds.HelfgottSmall.Chunk.C0955
import RSBounds.HelfgottSmall.Chunk.C0956
import RSBounds.HelfgottSmall.Chunk.C0957
import RSBounds.HelfgottSmall.Chunk.C0958
import RSBounds.HelfgottSmall.Chunk.C0959
import RSBounds.HelfgottSmall.Chunk.C0960
import RSBounds.HelfgottSmall.Chunk.C0961
import RSBounds.HelfgottSmall.Chunk.C0962
import RSBounds.HelfgottSmall.Chunk.C0963
import RSBounds.HelfgottSmall.Chunk.C0964
import RSBounds.HelfgottSmall.Chunk.C0965
import RSBounds.HelfgottSmall.Chunk.C0966
import RSBounds.HelfgottSmall.Chunk.C0967
import RSBounds.HelfgottSmall.Chunk.C0968
import RSBounds.HelfgottSmall.Chunk.C0969
import RSBounds.HelfgottSmall.Chunk.C0970
import RSBounds.HelfgottSmall.Chunk.C0971
import RSBounds.HelfgottSmall.Chunk.C0972
import RSBounds.HelfgottSmall.Chunk.C0973
import RSBounds.HelfgottSmall.Chunk.C0974
import RSBounds.HelfgottSmall.Chunk.C0975
import RSBounds.HelfgottSmall.Chunk.C0976
import RSBounds.HelfgottSmall.Chunk.C0977
import RSBounds.HelfgottSmall.Chunk.C0978
import RSBounds.HelfgottSmall.Chunk.C0979
import RSBounds.HelfgottSmall.Chunk.C0980
import RSBounds.HelfgottSmall.Chunk.C0981
import RSBounds.HelfgottSmall.Chunk.C0982
import RSBounds.HelfgottSmall.Chunk.C0983
import RSBounds.HelfgottSmall.Chunk.C0984
import RSBounds.HelfgottSmall.Chunk.C0985
import RSBounds.HelfgottSmall.Chunk.C0986
import RSBounds.HelfgottSmall.Chunk.C0987
import RSBounds.HelfgottSmall.Chunk.C0988
import RSBounds.HelfgottSmall.Chunk.C0989
import RSBounds.HelfgottSmall.Chunk.C0990
import RSBounds.HelfgottSmall.Chunk.C0991
import RSBounds.HelfgottSmall.Chunk.C0992
import RSBounds.HelfgottSmall.Chunk.C0993
import RSBounds.HelfgottSmall.Chunk.C0994
import RSBounds.HelfgottSmall.Chunk.C0995
import RSBounds.HelfgottSmall.Chunk.C0996
import RSBounds.HelfgottSmall.Chunk.C0997
import RSBounds.HelfgottSmall.Chunk.C0998
import RSBounds.HelfgottSmall.Chunk.C0999

/-! Walk chunks 950 to 999. -/

namespace RSBounds.HelfgottSmall

theorem group_19 (t : Nat) (ht : t < 50) : ChunkGood (950 + t) :=
  match t, ht with
  | 0, _ => chunk_950
  | 1, _ => chunk_951
  | 2, _ => chunk_952
  | 3, _ => chunk_953
  | 4, _ => chunk_954
  | 5, _ => chunk_955
  | 6, _ => chunk_956
  | 7, _ => chunk_957
  | 8, _ => chunk_958
  | 9, _ => chunk_959
  | 10, _ => chunk_960
  | 11, _ => chunk_961
  | 12, _ => chunk_962
  | 13, _ => chunk_963
  | 14, _ => chunk_964
  | 15, _ => chunk_965
  | 16, _ => chunk_966
  | 17, _ => chunk_967
  | 18, _ => chunk_968
  | 19, _ => chunk_969
  | 20, _ => chunk_970
  | 21, _ => chunk_971
  | 22, _ => chunk_972
  | 23, _ => chunk_973
  | 24, _ => chunk_974
  | 25, _ => chunk_975
  | 26, _ => chunk_976
  | 27, _ => chunk_977
  | 28, _ => chunk_978
  | 29, _ => chunk_979
  | 30, _ => chunk_980
  | 31, _ => chunk_981
  | 32, _ => chunk_982
  | 33, _ => chunk_983
  | 34, _ => chunk_984
  | 35, _ => chunk_985
  | 36, _ => chunk_986
  | 37, _ => chunk_987
  | 38, _ => chunk_988
  | 39, _ => chunk_989
  | 40, _ => chunk_990
  | 41, _ => chunk_991
  | 42, _ => chunk_992
  | 43, _ => chunk_993
  | 44, _ => chunk_994
  | 45, _ => chunk_995
  | 46, _ => chunk_996
  | 47, _ => chunk_997
  | 48, _ => chunk_998
  | 49, _ => chunk_999
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
