import RSBounds.HelfgottSmall.States

/-! Walk chunk 7, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_7 : RSBounds.HelfgottSmall.ChunkGood 7 := by
  decide +kernel
