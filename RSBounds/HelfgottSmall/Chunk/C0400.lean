import RSBounds.HelfgottSmall.States

/-! Walk chunk 400, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_400 : RSBounds.HelfgottSmall.ChunkGood 400 := by
  decide +kernel
