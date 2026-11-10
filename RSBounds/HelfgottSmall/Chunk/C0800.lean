import RSBounds.HelfgottSmall.States

/-! Walk chunk 800, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_800 : RSBounds.HelfgottSmall.ChunkGood 800 := by
  decide +kernel
