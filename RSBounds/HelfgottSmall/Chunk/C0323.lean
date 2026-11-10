import RSBounds.HelfgottSmall.States

/-! Walk chunk 323, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_323 : RSBounds.HelfgottSmall.ChunkGood 323 := by
  decide +kernel
