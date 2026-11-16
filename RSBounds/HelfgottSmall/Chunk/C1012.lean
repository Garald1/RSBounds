import RSBounds.HelfgottSmall.States

/-! Walk chunk 1012, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1012 : RSBounds.HelfgottSmall.ChunkGood 1012 := by
  decide +kernel
