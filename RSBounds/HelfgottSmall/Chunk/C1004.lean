import RSBounds.HelfgottSmall.States

/-! Walk chunk 1004, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1004 : RSBounds.HelfgottSmall.ChunkGood 1004 := by
  decide +kernel
