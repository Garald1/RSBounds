import RSBounds.HelfgottSmall.States

/-! Walk chunk 220, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_220 : RSBounds.HelfgottSmall.ChunkGood 220 := by
  decide +kernel
