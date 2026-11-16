import RSBounds.HelfgottSmall.States

/-! Walk chunk 105, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_105 : RSBounds.HelfgottSmall.ChunkGood 105 := by
  decide +kernel
