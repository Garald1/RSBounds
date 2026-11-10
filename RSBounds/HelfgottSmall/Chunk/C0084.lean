import RSBounds.HelfgottSmall.States

/-! Walk chunk 84, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_84 : RSBounds.HelfgottSmall.ChunkGood 84 := by
  decide +kernel
