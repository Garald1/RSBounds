import RSBounds.HelfgottSmall.States

/-! Walk chunk 24, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_24 : RSBounds.HelfgottSmall.ChunkGood 24 := by
  decide +kernel
