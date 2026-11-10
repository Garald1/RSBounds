import RSBounds.HelfgottSmall.States

/-! Walk chunk 1, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1 : RSBounds.HelfgottSmall.ChunkGood 1 := by
  decide +kernel
