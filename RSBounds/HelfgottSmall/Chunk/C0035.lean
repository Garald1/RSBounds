import RSBounds.HelfgottSmall.States

/-! Walk chunk 35, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_35 : RSBounds.HelfgottSmall.ChunkGood 35 := by
  decide +kernel
