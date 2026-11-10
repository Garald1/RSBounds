import RSBounds.HelfgottSmall.States

/-! Walk chunk 760, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_760 : RSBounds.HelfgottSmall.ChunkGood 760 := by
  decide +kernel
