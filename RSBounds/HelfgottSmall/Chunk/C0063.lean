import RSBounds.HelfgottSmall.States

/-! Walk chunk 63, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_63 : RSBounds.HelfgottSmall.ChunkGood 63 := by
  decide +kernel
