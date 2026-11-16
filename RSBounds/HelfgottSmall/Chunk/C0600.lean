import RSBounds.HelfgottSmall.States

/-! Walk chunk 600, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_600 : RSBounds.HelfgottSmall.ChunkGood 600 := by
  decide +kernel
