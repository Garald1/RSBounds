import RSBounds.HelfgottSmall.States

/-! Walk chunk 122, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_122 : RSBounds.HelfgottSmall.ChunkGood 122 := by
  decide +kernel
