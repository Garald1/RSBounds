import RSBounds.HelfgottSmall.States

/-! Walk chunk 401, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_401 : RSBounds.HelfgottSmall.ChunkGood 401 := by
  decide +kernel
