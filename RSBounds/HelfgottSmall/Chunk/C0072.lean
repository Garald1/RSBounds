import RSBounds.HelfgottSmall.States

/-! Walk chunk 72, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_72 : RSBounds.HelfgottSmall.ChunkGood 72 := by
  decide +kernel
