import RSBounds.HelfgottSmall.States

/-! Walk chunk 313, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_313 : RSBounds.HelfgottSmall.ChunkGood 313 := by
  decide +kernel
