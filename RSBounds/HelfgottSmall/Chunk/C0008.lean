import RSBounds.HelfgottSmall.States

/-! Walk chunk 8, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_8 : RSBounds.HelfgottSmall.ChunkGood 8 := by
  decide +kernel
