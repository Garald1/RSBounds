import RSBounds.HelfgottSmall.States

/-! Walk chunk 26, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_26 : RSBounds.HelfgottSmall.ChunkGood 26 := by
  decide +kernel
