import RSBounds.HelfgottSmall.States

/-! Walk chunk 85, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_85 : RSBounds.HelfgottSmall.ChunkGood 85 := by
  decide +kernel
