import RSBounds.HelfgottSmall.States

/-! Walk chunk 4, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_4 : RSBounds.HelfgottSmall.ChunkGood 4 := by
  decide +kernel
