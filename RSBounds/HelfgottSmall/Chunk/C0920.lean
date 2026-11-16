import RSBounds.HelfgottSmall.States

/-! Walk chunk 920, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_920 : RSBounds.HelfgottSmall.ChunkGood 920 := by
  decide +kernel
