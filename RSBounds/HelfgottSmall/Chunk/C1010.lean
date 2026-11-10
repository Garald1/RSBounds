import RSBounds.HelfgottSmall.States

/-! Walk chunk 1010, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1010 : RSBounds.HelfgottSmall.ChunkGood 1010 := by
  decide +kernel
