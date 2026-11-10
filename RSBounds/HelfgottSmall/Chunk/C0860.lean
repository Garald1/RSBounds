import RSBounds.HelfgottSmall.States

/-! Walk chunk 860, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_860 : RSBounds.HelfgottSmall.ChunkGood 860 := by
  decide +kernel
