import RSBounds.HelfgottSmall.States

/-! Walk chunk 365, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_365 : RSBounds.HelfgottSmall.ChunkGood 365 := by
  decide +kernel
