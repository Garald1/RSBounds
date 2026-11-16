import RSBounds.HelfgottSmall.States

/-! Walk chunk 601, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_601 : RSBounds.HelfgottSmall.ChunkGood 601 := by
  decide +kernel
