import RSBounds.HelfgottSmall.States

/-! Walk chunk 308, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_308 : RSBounds.HelfgottSmall.ChunkGood 308 := by
  decide +kernel
