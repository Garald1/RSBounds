import RSBounds.HelfgottSmall.States

/-! Walk chunk 299, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_299 : RSBounds.HelfgottSmall.ChunkGood 299 := by
  decide +kernel
