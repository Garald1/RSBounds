import RSBounds.HelfgottSmall.States

/-! Walk chunk 76, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_76 : RSBounds.HelfgottSmall.ChunkGood 76 := by
  decide +kernel
