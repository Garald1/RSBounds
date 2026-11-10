import RSBounds.HelfgottSmall.States

/-! Walk chunk 6, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_6 : RSBounds.HelfgottSmall.ChunkGood 6 := by
  decide +kernel
