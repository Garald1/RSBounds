import RSBounds.HelfgottSmall.States

/-! Walk chunk 52, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_52 : RSBounds.HelfgottSmall.ChunkGood 52 := by
  decide +kernel
