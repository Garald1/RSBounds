import RSBounds.HelfgottSmall.States

/-! Walk chunk 75, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_75 : RSBounds.HelfgottSmall.ChunkGood 75 := by
  decide +kernel
