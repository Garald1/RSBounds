import RSBounds.HelfgottSmall.States

/-! Walk chunk 970, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_970 : RSBounds.HelfgottSmall.ChunkGood 970 := by
  decide +kernel
