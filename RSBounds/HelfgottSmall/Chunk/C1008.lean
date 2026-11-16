import RSBounds.HelfgottSmall.States

/-! Walk chunk 1008, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1008 : RSBounds.HelfgottSmall.ChunkGood 1008 := by
  decide +kernel
