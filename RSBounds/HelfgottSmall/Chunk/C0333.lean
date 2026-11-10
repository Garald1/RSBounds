import RSBounds.HelfgottSmall.States

/-! Walk chunk 333, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_333 : RSBounds.HelfgottSmall.ChunkGood 333 := by
  decide +kernel
