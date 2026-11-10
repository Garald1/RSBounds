import RSBounds.HelfgottSmall.States

/-! Walk chunk 660, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_660 : RSBounds.HelfgottSmall.ChunkGood 660 := by
  decide +kernel
