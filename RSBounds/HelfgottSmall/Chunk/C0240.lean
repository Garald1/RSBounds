import RSBounds.HelfgottSmall.States

/-! Walk chunk 240, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_240 : RSBounds.HelfgottSmall.ChunkGood 240 := by
  decide +kernel
