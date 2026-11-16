import RSBounds.HelfgottSmall.States

/-! Walk chunk 1024, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1024 : RSBounds.HelfgottSmall.ChunkGood 1024 := by
  decide +kernel
