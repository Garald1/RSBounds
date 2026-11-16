import RSBounds.HelfgottSmall.States

/-! Walk chunk 60, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_60 : RSBounds.HelfgottSmall.ChunkGood 60 := by
  decide +kernel
