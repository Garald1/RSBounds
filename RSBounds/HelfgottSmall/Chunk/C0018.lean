import RSBounds.HelfgottSmall.States

/-! Walk chunk 18, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_18 : RSBounds.HelfgottSmall.ChunkGood 18 := by
  decide +kernel
