import RSBounds.HelfgottSmall.States

/-! Walk chunk 485, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_485 : RSBounds.HelfgottSmall.ChunkGood 485 := by
  decide +kernel
