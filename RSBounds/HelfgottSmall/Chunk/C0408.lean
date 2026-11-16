import RSBounds.HelfgottSmall.States

/-! Walk chunk 408, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_408 : RSBounds.HelfgottSmall.ChunkGood 408 := by
  decide +kernel
