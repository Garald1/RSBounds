import RSBounds.HelfgottSmall.States

/-! Walk chunk 411, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_411 : RSBounds.HelfgottSmall.ChunkGood 411 := by
  decide +kernel
