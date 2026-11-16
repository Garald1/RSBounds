import RSBounds.HelfgottSmall.States

/-! Walk chunk 789, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_789 : RSBounds.HelfgottSmall.ChunkGood 789 := by
  decide +kernel
