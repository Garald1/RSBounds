import RSBounds.HelfgottSmall.States

/-! Walk chunk 56, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_56 : RSBounds.HelfgottSmall.ChunkGood 56 := by
  decide +kernel
