import RSBounds.HelfgottSmall.States

/-! Walk chunk 360, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_360 : RSBounds.HelfgottSmall.ChunkGood 360 := by
  decide +kernel
