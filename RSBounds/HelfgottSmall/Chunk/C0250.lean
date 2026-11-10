import RSBounds.HelfgottSmall.States

/-! Walk chunk 250, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_250 : RSBounds.HelfgottSmall.ChunkGood 250 := by
  decide +kernel
