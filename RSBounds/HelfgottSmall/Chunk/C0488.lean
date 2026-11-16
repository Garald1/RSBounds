import RSBounds.HelfgottSmall.States

/-! Walk chunk 488, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_488 : RSBounds.HelfgottSmall.ChunkGood 488 := by
  decide +kernel
