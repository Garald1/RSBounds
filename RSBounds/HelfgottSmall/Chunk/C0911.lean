import RSBounds.HelfgottSmall.States

/-! Walk chunk 911, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_911 : RSBounds.HelfgottSmall.ChunkGood 911 := by
  decide +kernel
