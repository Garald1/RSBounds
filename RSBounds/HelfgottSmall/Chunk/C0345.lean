import RSBounds.HelfgottSmall.States

/-! Walk chunk 345, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_345 : RSBounds.HelfgottSmall.ChunkGood 345 := by
  decide +kernel
