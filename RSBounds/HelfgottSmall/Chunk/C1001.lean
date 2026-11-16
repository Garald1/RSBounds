import RSBounds.HelfgottSmall.States

/-! Walk chunk 1001, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1001 : RSBounds.HelfgottSmall.ChunkGood 1001 := by
  decide +kernel
