import RSBounds.HelfgottSmall.States

/-! Walk chunk 603, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_603 : RSBounds.HelfgottSmall.ChunkGood 603 := by
  decide +kernel
