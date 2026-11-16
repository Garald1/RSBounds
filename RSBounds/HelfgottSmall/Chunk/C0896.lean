import RSBounds.HelfgottSmall.States

/-! Walk chunk 896, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_896 : RSBounds.HelfgottSmall.ChunkGood 896 := by
  decide +kernel
