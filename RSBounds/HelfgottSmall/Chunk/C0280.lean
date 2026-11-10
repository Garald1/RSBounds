import RSBounds.HelfgottSmall.States

/-! Walk chunk 280, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_280 : RSBounds.HelfgottSmall.ChunkGood 280 := by
  decide +kernel
