import RSBounds.HelfgottSmall.States

/-! Walk chunk 260, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_260 : RSBounds.HelfgottSmall.ChunkGood 260 := by
  decide +kernel
