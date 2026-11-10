import RSBounds.HelfgottSmall.States

/-! Walk chunk 98, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_98 : RSBounds.HelfgottSmall.ChunkGood 98 := by
  decide +kernel
