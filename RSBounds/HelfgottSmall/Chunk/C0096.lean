import RSBounds.HelfgottSmall.States

/-! Walk chunk 96, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_96 : RSBounds.HelfgottSmall.ChunkGood 96 := by
  decide +kernel
