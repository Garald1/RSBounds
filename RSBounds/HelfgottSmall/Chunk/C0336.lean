import RSBounds.HelfgottSmall.States

/-! Walk chunk 336, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_336 : RSBounds.HelfgottSmall.ChunkGood 336 := by
  decide +kernel
