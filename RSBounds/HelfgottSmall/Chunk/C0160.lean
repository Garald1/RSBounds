import RSBounds.HelfgottSmall.States

/-! Walk chunk 160, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_160 : RSBounds.HelfgottSmall.ChunkGood 160 := by
  decide +kernel
