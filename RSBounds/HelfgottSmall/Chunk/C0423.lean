import RSBounds.HelfgottSmall.States

/-! Walk chunk 423, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_423 : RSBounds.HelfgottSmall.ChunkGood 423 := by
  decide +kernel
