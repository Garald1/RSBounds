import RSBounds.HelfgottSmall.States

/-! Walk chunk 304, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_304 : RSBounds.HelfgottSmall.ChunkGood 304 := by
  decide +kernel
