import RSBounds.HelfgottSmall.States

/-! Walk chunk 150, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_150 : RSBounds.HelfgottSmall.ChunkGood 150 := by
  decide +kernel
