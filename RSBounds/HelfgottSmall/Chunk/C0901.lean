import RSBounds.HelfgottSmall.States

/-! Walk chunk 901, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_901 : RSBounds.HelfgottSmall.ChunkGood 901 := by
  decide +kernel
