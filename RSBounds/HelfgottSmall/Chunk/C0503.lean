import RSBounds.HelfgottSmall.States

/-! Walk chunk 503, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_503 : RSBounds.HelfgottSmall.ChunkGood 503 := by
  decide +kernel
