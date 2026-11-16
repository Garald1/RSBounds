import RSBounds.HelfgottSmall.States

/-! Walk chunk 44, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_44 : RSBounds.HelfgottSmall.ChunkGood 44 := by
  decide +kernel
