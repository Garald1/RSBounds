import RSBounds.HelfgottSmall.States

/-! Walk chunk 1231, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1231 : RSBounds.HelfgottSmall.ChunkGood 1231 := by
  decide +kernel
