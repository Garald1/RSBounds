import RSBounds.HelfgottSmall.States

/-! Walk chunk 1112, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1112 : RSBounds.HelfgottSmall.ChunkGood 1112 := by
  decide +kernel
