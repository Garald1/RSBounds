import RSBounds.HelfgottSmall.States

/-! Walk chunk 1025, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1025 : RSBounds.HelfgottSmall.ChunkGood 1025 := by
  decide +kernel
