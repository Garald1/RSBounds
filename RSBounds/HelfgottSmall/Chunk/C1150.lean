import RSBounds.HelfgottSmall.States

/-! Walk chunk 1150, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1150 : RSBounds.HelfgottSmall.ChunkGood 1150 := by
  decide +kernel
