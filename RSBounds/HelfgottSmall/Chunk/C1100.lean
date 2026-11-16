import RSBounds.HelfgottSmall.States

/-! Walk chunk 1100, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1100 : RSBounds.HelfgottSmall.ChunkGood 1100 := by
  decide +kernel
