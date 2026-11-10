import RSBounds.HelfgottSmall.States

/-! Walk chunk 66, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_66 : RSBounds.HelfgottSmall.ChunkGood 66 := by
  decide +kernel
