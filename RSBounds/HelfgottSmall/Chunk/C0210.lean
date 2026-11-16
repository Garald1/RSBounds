import RSBounds.HelfgottSmall.States

/-! Walk chunk 210, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_210 : RSBounds.HelfgottSmall.ChunkGood 210 := by
  decide +kernel
