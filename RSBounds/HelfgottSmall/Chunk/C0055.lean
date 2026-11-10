import RSBounds.HelfgottSmall.States

/-! Walk chunk 55, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_55 : RSBounds.HelfgottSmall.ChunkGood 55 := by
  decide +kernel
