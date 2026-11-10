import RSBounds.HelfgottSmall.States

/-! Walk chunk 1040, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1040 : RSBounds.HelfgottSmall.ChunkGood 1040 := by
  decide +kernel
