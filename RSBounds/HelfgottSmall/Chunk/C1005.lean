import RSBounds.HelfgottSmall.States

/-! Walk chunk 1005, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1005 : RSBounds.HelfgottSmall.ChunkGood 1005 := by
  decide +kernel
