import RSBounds.HelfgottSmall.States

/-! Walk chunk 199, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_199 : RSBounds.HelfgottSmall.ChunkGood 199 := by
  decide +kernel
