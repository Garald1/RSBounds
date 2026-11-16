import RSBounds.HelfgottSmall.States

/-! Walk chunk 70, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_70 : RSBounds.HelfgottSmall.ChunkGood 70 := by
  decide +kernel
