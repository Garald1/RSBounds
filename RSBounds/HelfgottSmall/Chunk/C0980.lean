import RSBounds.HelfgottSmall.States

/-! Walk chunk 980, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_980 : RSBounds.HelfgottSmall.ChunkGood 980 := by
  decide +kernel
