import RSBounds.HelfgottSmall.States

/-! Walk chunk 992, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_992 : RSBounds.HelfgottSmall.ChunkGood 992 := by
  decide +kernel
