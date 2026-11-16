import RSBounds.HelfgottSmall.States

/-! Walk chunk 987, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_987 : RSBounds.HelfgottSmall.ChunkGood 987 := by
  decide +kernel
