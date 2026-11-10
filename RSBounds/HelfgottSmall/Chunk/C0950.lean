import RSBounds.HelfgottSmall.States

/-! Walk chunk 950, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_950 : RSBounds.HelfgottSmall.ChunkGood 950 := by
  decide +kernel
