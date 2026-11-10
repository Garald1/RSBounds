import RSBounds.HelfgottSmall.States

/-! Walk chunk 20, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_20 : RSBounds.HelfgottSmall.ChunkGood 20 := by
  decide +kernel
