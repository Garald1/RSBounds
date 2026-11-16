import RSBounds.HelfgottSmall.States

/-! Walk chunk 505, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_505 : RSBounds.HelfgottSmall.ChunkGood 505 := by
  decide +kernel
