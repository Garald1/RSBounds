import RSBounds.HelfgottSmall.States

/-! Walk chunk 51, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_51 : RSBounds.HelfgottSmall.ChunkGood 51 := by
  decide +kernel
