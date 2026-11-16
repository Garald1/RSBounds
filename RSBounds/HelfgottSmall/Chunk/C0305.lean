import RSBounds.HelfgottSmall.States

/-! Walk chunk 305, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_305 : RSBounds.HelfgottSmall.ChunkGood 305 := by
  decide +kernel
