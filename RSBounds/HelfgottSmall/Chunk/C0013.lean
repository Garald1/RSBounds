import RSBounds.HelfgottSmall.States

/-! Walk chunk 13, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_13 : RSBounds.HelfgottSmall.ChunkGood 13 := by
  decide +kernel
