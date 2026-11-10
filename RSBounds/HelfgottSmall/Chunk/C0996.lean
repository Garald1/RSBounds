import RSBounds.HelfgottSmall.States

/-! Walk chunk 996, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_996 : RSBounds.HelfgottSmall.ChunkGood 996 := by
  decide +kernel
