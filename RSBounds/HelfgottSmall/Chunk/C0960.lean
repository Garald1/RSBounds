import RSBounds.HelfgottSmall.States

/-! Walk chunk 960, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_960 : RSBounds.HelfgottSmall.ChunkGood 960 := by
  decide +kernel
