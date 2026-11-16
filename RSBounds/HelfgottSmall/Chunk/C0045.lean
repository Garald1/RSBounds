import RSBounds.HelfgottSmall.States

/-! Walk chunk 45, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_45 : RSBounds.HelfgottSmall.ChunkGood 45 := by
  decide +kernel
