import RSBounds.HelfgottSmall.States

/-! Walk chunk 64, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_64 : RSBounds.HelfgottSmall.ChunkGood 64 := by
  decide +kernel
