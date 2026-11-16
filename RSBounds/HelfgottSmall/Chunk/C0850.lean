import RSBounds.HelfgottSmall.States

/-! Walk chunk 850, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_850 : RSBounds.HelfgottSmall.ChunkGood 850 := by
  decide +kernel
