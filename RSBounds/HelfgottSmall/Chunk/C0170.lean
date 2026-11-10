import RSBounds.HelfgottSmall.States

/-! Walk chunk 170, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_170 : RSBounds.HelfgottSmall.ChunkGood 170 := by
  decide +kernel
