import RSBounds.HelfgottSmall.States

/-! Walk chunk 909, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_909 : RSBounds.HelfgottSmall.ChunkGood 909 := by
  decide +kernel
