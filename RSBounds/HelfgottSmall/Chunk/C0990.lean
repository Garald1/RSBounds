import RSBounds.HelfgottSmall.States

/-! Walk chunk 990, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_990 : RSBounds.HelfgottSmall.ChunkGood 990 := by
  decide +kernel
