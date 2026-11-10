import RSBounds.HelfgottSmall.States

/-! Walk chunk 1130, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1130 : RSBounds.HelfgottSmall.ChunkGood 1130 := by
  decide +kernel
