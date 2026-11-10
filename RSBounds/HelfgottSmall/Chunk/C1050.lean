import RSBounds.HelfgottSmall.States

/-! Walk chunk 1050, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1050 : RSBounds.HelfgottSmall.ChunkGood 1050 := by
  decide +kernel
