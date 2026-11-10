import RSBounds.HelfgottSmall.States

/-! Walk chunk 10, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_10 : RSBounds.HelfgottSmall.ChunkGood 10 := by
  decide +kernel
