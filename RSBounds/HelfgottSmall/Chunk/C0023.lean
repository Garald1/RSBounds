import RSBounds.HelfgottSmall.States

/-! Walk chunk 23, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_23 : RSBounds.HelfgottSmall.ChunkGood 23 := by
  decide +kernel
