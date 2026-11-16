import RSBounds.HelfgottSmall.States

/-! Walk chunk 180, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_180 : RSBounds.HelfgottSmall.ChunkGood 180 := by
  decide +kernel
