import RSBounds.HelfgottSmall.States

/-! Walk chunk 1180, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1180 : RSBounds.HelfgottSmall.ChunkGood 1180 := by
  decide +kernel
