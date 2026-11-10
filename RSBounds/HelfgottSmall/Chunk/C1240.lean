import RSBounds.HelfgottSmall.States

/-! Walk chunk 1240, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1240 : RSBounds.HelfgottSmall.ChunkGood 1240 := by
  decide +kernel
