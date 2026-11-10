import RSBounds.HelfgottSmall.States

/-! Walk chunk 433, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_433 : RSBounds.HelfgottSmall.ChunkGood 433 := by
  decide +kernel
