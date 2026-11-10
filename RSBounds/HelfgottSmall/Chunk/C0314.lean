import RSBounds.HelfgottSmall.States

/-! Walk chunk 314, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_314 : RSBounds.HelfgottSmall.ChunkGood 314 := by
  decide +kernel
