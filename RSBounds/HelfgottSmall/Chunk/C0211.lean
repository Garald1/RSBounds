import RSBounds.HelfgottSmall.States

/-! Walk chunk 211, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_211 : RSBounds.HelfgottSmall.ChunkGood 211 := by
  decide +kernel
