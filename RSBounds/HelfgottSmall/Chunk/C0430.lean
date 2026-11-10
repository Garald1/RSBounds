import RSBounds.HelfgottSmall.States

/-! Walk chunk 430, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_430 : RSBounds.HelfgottSmall.ChunkGood 430 := by
  decide +kernel
