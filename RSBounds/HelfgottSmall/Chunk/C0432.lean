import RSBounds.HelfgottSmall.States

/-! Walk chunk 432, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_432 : RSBounds.HelfgottSmall.ChunkGood 432 := by
  decide +kernel
