import RSBounds.HelfgottSmall.States

/-! Walk chunk 15, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_15 : RSBounds.HelfgottSmall.ChunkGood 15 := by
  decide +kernel
