import RSBounds.HelfgottSmall.States

/-! Walk chunk 1234, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1234 : RSBounds.HelfgottSmall.ChunkGood 1234 := by
  decide +kernel
