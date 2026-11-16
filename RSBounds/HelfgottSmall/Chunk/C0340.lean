import RSBounds.HelfgottSmall.States

/-! Walk chunk 340, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_340 : RSBounds.HelfgottSmall.ChunkGood 340 := by
  decide +kernel
