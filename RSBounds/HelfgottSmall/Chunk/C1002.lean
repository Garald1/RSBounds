import RSBounds.HelfgottSmall.States

/-! Walk chunk 1002, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1002 : RSBounds.HelfgottSmall.ChunkGood 1002 := by
  decide +kernel
