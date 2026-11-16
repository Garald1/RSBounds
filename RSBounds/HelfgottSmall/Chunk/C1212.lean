import RSBounds.HelfgottSmall.States

/-! Walk chunk 1212, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1212 : RSBounds.HelfgottSmall.ChunkGood 1212 := by
  decide +kernel
