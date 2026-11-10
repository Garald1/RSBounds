import RSBounds.HelfgottSmall.States

/-! Walk chunk 25, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_25 : RSBounds.HelfgottSmall.ChunkGood 25 := by
  decide +kernel
