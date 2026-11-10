import RSBounds.HelfgottSmall.States

/-! Walk chunk 2, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_2 : RSBounds.HelfgottSmall.ChunkGood 2 := by
  decide +kernel
