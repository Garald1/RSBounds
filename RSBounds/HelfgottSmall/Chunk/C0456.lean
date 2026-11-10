import RSBounds.HelfgottSmall.States

/-! Walk chunk 456, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_456 : RSBounds.HelfgottSmall.ChunkGood 456 := by
  decide +kernel
