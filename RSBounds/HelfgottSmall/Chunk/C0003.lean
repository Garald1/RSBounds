import RSBounds.HelfgottSmall.States

/-! Walk chunk 3, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_3 : RSBounds.HelfgottSmall.ChunkGood 3 := by
  decide +kernel
