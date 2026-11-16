import RSBounds.HelfgottSmall.States

/-! Walk chunk 1210, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1210 : RSBounds.HelfgottSmall.ChunkGood 1210 := by
  decide +kernel
