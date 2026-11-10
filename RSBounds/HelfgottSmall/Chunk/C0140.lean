import RSBounds.HelfgottSmall.States

/-! Walk chunk 140, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_140 : RSBounds.HelfgottSmall.ChunkGood 140 := by
  decide +kernel
