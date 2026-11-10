import RSBounds.HelfgottSmall.States

/-! Walk chunk 100, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_100 : RSBounds.HelfgottSmall.ChunkGood 100 := by
  decide +kernel
