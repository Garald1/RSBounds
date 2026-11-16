import RSBounds.HelfgottSmall.States

/-! Walk chunk 102, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_102 : RSBounds.HelfgottSmall.ChunkGood 102 := by
  decide +kernel
