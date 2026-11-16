import RSBounds.HelfgottSmall.States

/-! Walk chunk 940, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_940 : RSBounds.HelfgottSmall.ChunkGood 940 := by
  decide +kernel
