import RSBounds.HelfgottSmall.States

/-! Walk chunk 312, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_312 : RSBounds.HelfgottSmall.ChunkGood 312 := by
  decide +kernel
