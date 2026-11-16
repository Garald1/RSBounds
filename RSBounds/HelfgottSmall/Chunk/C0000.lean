import RSBounds.HelfgottSmall.Chunk.C0000S0
import RSBounds.HelfgottSmall.Chunk.C0000S1
import RSBounds.HelfgottSmall.Chunk.C0000S2
import RSBounds.HelfgottSmall.Chunk.C0000S3
import RSBounds.HelfgottSmall.Chunk.C0000S4
import RSBounds.HelfgottSmall.Chunk.C0000S5
import RSBounds.HelfgottSmall.Chunk.C0000S6
import RSBounds.HelfgottSmall.Chunk.C0000S7
import RSBounds.HelfgottSmall.Chunk.C0000S8
import RSBounds.HelfgottSmall.Chunk.C0000S9

/-! Walk chunk 0, from its ten parts. -/

namespace RSBounds.HelfgottSmall

theorem chunk_0 : ChunkGood 0 := by
  have h := chunkOK_split chunk_0_part_0 (chunkOK_split chunk_0_part_1 (chunkOK_split chunk_0_part_2 (chunkOK_split chunk_0_part_3 (chunkOK_split chunk_0_part_4 (chunkOK_split chunk_0_part_5 (chunkOK_split chunk_0_part_6 (chunkOK_split chunk_0_part_7 (chunkOK_split chunk_0_part_8 (chunk_0_part_9)))))))))
  have hf : fuelOf 0 = 2000 + (2000 + (2000 + (2000 + (2000 + (2000 + (2000 + (2000 + (2000 + (2000))))))))) := by decide +kernel
  have h0 : stEq (stateOf 0)
      (2, 0, 0, 0, 2, 693147180800000, 3, 0, 4, 2) = true := by decide +kernel
  have h1 : stEq (stateOf (0 + 1))
      (20002, 19976518807272000996, 199578084351016601655550, 1234, 19912, 9899077844887692, 20011, 66, 22201, 2) = true := by decide +kernel
  unfold ChunkGood
  rw [hf, stEq_eq' h0, stEq_eq' h1]
  exact h

end RSBounds.HelfgottSmall
