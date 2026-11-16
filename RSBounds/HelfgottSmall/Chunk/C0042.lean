import RSBounds.HelfgottSmall.States

/-! Walk chunk 42, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_42 : RSBounds.HelfgottSmall.ChunkGood 42 := by
  decide +kernel
