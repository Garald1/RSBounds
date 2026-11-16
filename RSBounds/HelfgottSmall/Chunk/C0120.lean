import RSBounds.HelfgottSmall.States

/-! Walk chunk 120, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_120 : RSBounds.HelfgottSmall.ChunkGood 120 := by
  decide +kernel
