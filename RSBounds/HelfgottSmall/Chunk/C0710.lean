import RSBounds.HelfgottSmall.States

/-! Walk chunk 710, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_710 : RSBounds.HelfgottSmall.ChunkGood 710 := by
  decide +kernel
