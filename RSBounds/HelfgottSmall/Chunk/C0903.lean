import RSBounds.HelfgottSmall.States

/-! Walk chunk 903, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_903 : RSBounds.HelfgottSmall.ChunkGood 903 := by
  decide +kernel
