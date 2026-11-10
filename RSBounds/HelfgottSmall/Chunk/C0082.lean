import RSBounds.HelfgottSmall.States

/-! Walk chunk 82, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_82 : RSBounds.HelfgottSmall.ChunkGood 82 := by
  decide +kernel
