import RSBounds.HelfgottSmall.States

/-! Walk chunk 81, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_81 : RSBounds.HelfgottSmall.ChunkGood 81 := by
  decide +kernel
