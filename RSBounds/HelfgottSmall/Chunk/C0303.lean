import RSBounds.HelfgottSmall.States

/-! Walk chunk 303, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_303 : RSBounds.HelfgottSmall.ChunkGood 303 := by
  decide +kernel
