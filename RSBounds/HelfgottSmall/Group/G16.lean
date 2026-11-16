import RSBounds.HelfgottSmall.Chunk.C0800
import RSBounds.HelfgottSmall.Chunk.C0801
import RSBounds.HelfgottSmall.Chunk.C0802
import RSBounds.HelfgottSmall.Chunk.C0803
import RSBounds.HelfgottSmall.Chunk.C0804
import RSBounds.HelfgottSmall.Chunk.C0805
import RSBounds.HelfgottSmall.Chunk.C0806
import RSBounds.HelfgottSmall.Chunk.C0807
import RSBounds.HelfgottSmall.Chunk.C0808
import RSBounds.HelfgottSmall.Chunk.C0809
import RSBounds.HelfgottSmall.Chunk.C0810
import RSBounds.HelfgottSmall.Chunk.C0811
import RSBounds.HelfgottSmall.Chunk.C0812
import RSBounds.HelfgottSmall.Chunk.C0813
import RSBounds.HelfgottSmall.Chunk.C0814
import RSBounds.HelfgottSmall.Chunk.C0815
import RSBounds.HelfgottSmall.Chunk.C0816
import RSBounds.HelfgottSmall.Chunk.C0817
import RSBounds.HelfgottSmall.Chunk.C0818
import RSBounds.HelfgottSmall.Chunk.C0819
import RSBounds.HelfgottSmall.Chunk.C0820
import RSBounds.HelfgottSmall.Chunk.C0821
import RSBounds.HelfgottSmall.Chunk.C0822
import RSBounds.HelfgottSmall.Chunk.C0823
import RSBounds.HelfgottSmall.Chunk.C0824
import RSBounds.HelfgottSmall.Chunk.C0825
import RSBounds.HelfgottSmall.Chunk.C0826
import RSBounds.HelfgottSmall.Chunk.C0827
import RSBounds.HelfgottSmall.Chunk.C0828
import RSBounds.HelfgottSmall.Chunk.C0829
import RSBounds.HelfgottSmall.Chunk.C0830
import RSBounds.HelfgottSmall.Chunk.C0831
import RSBounds.HelfgottSmall.Chunk.C0832
import RSBounds.HelfgottSmall.Chunk.C0833
import RSBounds.HelfgottSmall.Chunk.C0834
import RSBounds.HelfgottSmall.Chunk.C0835
import RSBounds.HelfgottSmall.Chunk.C0836
import RSBounds.HelfgottSmall.Chunk.C0837
import RSBounds.HelfgottSmall.Chunk.C0838
import RSBounds.HelfgottSmall.Chunk.C0839
import RSBounds.HelfgottSmall.Chunk.C0840
import RSBounds.HelfgottSmall.Chunk.C0841
import RSBounds.HelfgottSmall.Chunk.C0842
import RSBounds.HelfgottSmall.Chunk.C0843
import RSBounds.HelfgottSmall.Chunk.C0844
import RSBounds.HelfgottSmall.Chunk.C0845
import RSBounds.HelfgottSmall.Chunk.C0846
import RSBounds.HelfgottSmall.Chunk.C0847
import RSBounds.HelfgottSmall.Chunk.C0848
import RSBounds.HelfgottSmall.Chunk.C0849

/-! Walk chunks 800 to 849. -/

namespace RSBounds.HelfgottSmall

theorem group_16 (t : Nat) (ht : t < 50) : ChunkGood (800 + t) :=
  match t, ht with
  | 0, _ => chunk_800
  | 1, _ => chunk_801
  | 2, _ => chunk_802
  | 3, _ => chunk_803
  | 4, _ => chunk_804
  | 5, _ => chunk_805
  | 6, _ => chunk_806
  | 7, _ => chunk_807
  | 8, _ => chunk_808
  | 9, _ => chunk_809
  | 10, _ => chunk_810
  | 11, _ => chunk_811
  | 12, _ => chunk_812
  | 13, _ => chunk_813
  | 14, _ => chunk_814
  | 15, _ => chunk_815
  | 16, _ => chunk_816
  | 17, _ => chunk_817
  | 18, _ => chunk_818
  | 19, _ => chunk_819
  | 20, _ => chunk_820
  | 21, _ => chunk_821
  | 22, _ => chunk_822
  | 23, _ => chunk_823
  | 24, _ => chunk_824
  | 25, _ => chunk_825
  | 26, _ => chunk_826
  | 27, _ => chunk_827
  | 28, _ => chunk_828
  | 29, _ => chunk_829
  | 30, _ => chunk_830
  | 31, _ => chunk_831
  | 32, _ => chunk_832
  | 33, _ => chunk_833
  | 34, _ => chunk_834
  | 35, _ => chunk_835
  | 36, _ => chunk_836
  | 37, _ => chunk_837
  | 38, _ => chunk_838
  | 39, _ => chunk_839
  | 40, _ => chunk_840
  | 41, _ => chunk_841
  | 42, _ => chunk_842
  | 43, _ => chunk_843
  | 44, _ => chunk_844
  | 45, _ => chunk_845
  | 46, _ => chunk_846
  | 47, _ => chunk_847
  | 48, _ => chunk_848
  | 49, _ => chunk_849
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
