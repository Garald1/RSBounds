import RSBounds.HelfgottSmall.States

/-! Walk chunk 444, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_444 : RSBounds.HelfgottSmall.ChunkGood 444 := by
  decide +kernel
