import RSBounds.HelfgottSmall.States

/-! Walk chunk 89, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_89 : RSBounds.HelfgottSmall.ChunkGood 89 := by
  decide +kernel
