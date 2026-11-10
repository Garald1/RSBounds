import RSBounds.HelfgottSmall.States

/-! Walk chunk 21, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_21 : RSBounds.HelfgottSmall.ChunkGood 21 := by
  decide +kernel
