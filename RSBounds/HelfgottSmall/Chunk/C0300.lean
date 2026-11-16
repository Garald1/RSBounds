import RSBounds.HelfgottSmall.States

/-! Walk chunk 300, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_300 : RSBounds.HelfgottSmall.ChunkGood 300 := by
  decide +kernel
