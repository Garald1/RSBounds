import RSBounds.HelfgottSmall.States

/-! Walk chunk 16, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_16 : RSBounds.HelfgottSmall.ChunkGood 16 := by
  decide +kernel
