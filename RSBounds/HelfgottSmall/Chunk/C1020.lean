import RSBounds.HelfgottSmall.States

/-! Walk chunk 1020, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1020 : RSBounds.HelfgottSmall.ChunkGood 1020 := by
  decide +kernel
