import RSBounds.HelfgottSmall.States

/-! Walk chunk 127, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_127 : RSBounds.HelfgottSmall.ChunkGood 127 := by
  decide +kernel
