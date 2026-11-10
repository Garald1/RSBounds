import RSBounds.HelfgottSmall.States

/-! Walk chunk 644, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_644 : RSBounds.HelfgottSmall.ChunkGood 644 := by
  decide +kernel
