import RSBounds.HelfgottSmall.States

/-! Walk chunk 99, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_99 : RSBounds.HelfgottSmall.ChunkGood 99 := by
  decide +kernel
