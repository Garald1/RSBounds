import RSBounds.HelfgottSmall.States

/-! Walk chunk 750, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_750 : RSBounds.HelfgottSmall.ChunkGood 750 := by
  decide +kernel
