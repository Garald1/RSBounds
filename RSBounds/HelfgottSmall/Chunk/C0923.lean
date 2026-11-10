import RSBounds.HelfgottSmall.States

/-! Walk chunk 923, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_923 : RSBounds.HelfgottSmall.ChunkGood 923 := by
  decide +kernel
