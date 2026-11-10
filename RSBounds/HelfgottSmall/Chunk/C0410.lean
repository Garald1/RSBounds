import RSBounds.HelfgottSmall.States

/-! Walk chunk 410, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_410 : RSBounds.HelfgottSmall.ChunkGood 410 := by
  decide +kernel
