import RSBounds.HelfgottSmall.States

/-! Walk chunk 1016, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1016 : RSBounds.HelfgottSmall.ChunkGood 1016 := by
  decide +kernel
