import RSBounds.HelfgottSmall.States

/-! Walk chunk 112, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_112 : RSBounds.HelfgottSmall.ChunkGood 112 := by
  decide +kernel
