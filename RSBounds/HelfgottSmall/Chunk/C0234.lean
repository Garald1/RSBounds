import RSBounds.HelfgottSmall.States

/-! Walk chunk 234, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_234 : RSBounds.HelfgottSmall.ChunkGood 234 := by
  decide +kernel
