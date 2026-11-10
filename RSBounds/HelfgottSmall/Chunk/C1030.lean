import RSBounds.HelfgottSmall.States

/-! Walk chunk 1030, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1030 : RSBounds.HelfgottSmall.ChunkGood 1030 := by
  decide +kernel
