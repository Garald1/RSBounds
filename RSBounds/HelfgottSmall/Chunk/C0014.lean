import RSBounds.HelfgottSmall.States

/-! Walk chunk 14, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_14 : RSBounds.HelfgottSmall.ChunkGood 14 := by
  decide +kernel
