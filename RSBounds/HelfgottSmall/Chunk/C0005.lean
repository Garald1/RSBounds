import RSBounds.HelfgottSmall.States

/-! Walk chunk 5, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_5 : RSBounds.HelfgottSmall.ChunkGood 5 := by
  decide +kernel
