import RSBounds.HelfgottSmall.States

/-! Walk chunk 310, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_310 : RSBounds.HelfgottSmall.ChunkGood 310 := by
  decide +kernel
