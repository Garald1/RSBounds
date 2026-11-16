import RSBounds.HelfgottSmall.States

/-! Walk chunk 22, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_22 : RSBounds.HelfgottSmall.ChunkGood 22 := by
  decide +kernel
