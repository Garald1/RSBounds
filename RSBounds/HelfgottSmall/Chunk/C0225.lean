import RSBounds.HelfgottSmall.States

/-! Walk chunk 225, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_225 : RSBounds.HelfgottSmall.ChunkGood 225 := by
  decide +kernel
