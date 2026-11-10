import RSBounds.HelfgottSmall.States

/-! Walk chunk 11, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_11 : RSBounds.HelfgottSmall.ChunkGood 11 := by
  decide +kernel
