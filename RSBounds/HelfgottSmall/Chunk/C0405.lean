import RSBounds.HelfgottSmall.States

/-! Walk chunk 405, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_405 : RSBounds.HelfgottSmall.ChunkGood 405 := by
  decide +kernel
