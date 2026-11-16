import RSBounds.HelfgottSmall.States

/-! Walk chunk 402, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_402 : RSBounds.HelfgottSmall.ChunkGood 402 := by
  decide +kernel
