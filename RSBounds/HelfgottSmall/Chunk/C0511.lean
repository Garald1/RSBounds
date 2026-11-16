import RSBounds.HelfgottSmall.States

/-! Walk chunk 511, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_511 : RSBounds.HelfgottSmall.ChunkGood 511 := by
  decide +kernel
