import RSBounds.HelfgottSmall.States

/-! Walk chunk 343, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_343 : RSBounds.HelfgottSmall.ChunkGood 343 := by
  decide +kernel
