import RSBounds.HelfgottSmall.States

/-! Walk chunk 880, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_880 : RSBounds.HelfgottSmall.ChunkGood 880 := by
  decide +kernel
