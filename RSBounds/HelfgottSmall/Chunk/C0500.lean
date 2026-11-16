import RSBounds.HelfgottSmall.States

/-! Walk chunk 500, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_500 : RSBounds.HelfgottSmall.ChunkGood 500 := by
  decide +kernel
