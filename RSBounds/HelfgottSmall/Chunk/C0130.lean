import RSBounds.HelfgottSmall.States

/-! Walk chunk 130, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_130 : RSBounds.HelfgottSmall.ChunkGood 130 := by
  decide +kernel
