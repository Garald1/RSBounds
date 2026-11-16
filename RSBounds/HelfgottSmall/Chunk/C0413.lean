import RSBounds.HelfgottSmall.States

/-! Walk chunk 413, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_413 : RSBounds.HelfgottSmall.ChunkGood 413 := by
  decide +kernel
