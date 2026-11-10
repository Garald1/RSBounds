import RSBounds.HelfgottSmall.States

/-! Walk chunk 9, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_9 : RSBounds.HelfgottSmall.ChunkGood 9 := by
  decide +kernel
