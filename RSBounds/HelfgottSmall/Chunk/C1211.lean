import RSBounds.HelfgottSmall.States

/-! Walk chunk 1211, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1211 : RSBounds.HelfgottSmall.ChunkGood 1211 := by
  decide +kernel
