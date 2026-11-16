import RSBounds.HelfgottSmall.States

/-! Walk chunk 1120, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1120 : RSBounds.HelfgottSmall.ChunkGood 1120 := by
  decide +kernel
