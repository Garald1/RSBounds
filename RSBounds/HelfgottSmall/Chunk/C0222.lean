import RSBounds.HelfgottSmall.States

/-! Walk chunk 222, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_222 : RSBounds.HelfgottSmall.ChunkGood 222 := by
  decide +kernel
