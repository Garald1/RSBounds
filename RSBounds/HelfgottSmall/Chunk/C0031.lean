import RSBounds.HelfgottSmall.States

/-! Walk chunk 31, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_31 : RSBounds.HelfgottSmall.ChunkGood 31 := by
  decide +kernel
