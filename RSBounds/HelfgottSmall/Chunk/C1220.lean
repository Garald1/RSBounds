import RSBounds.HelfgottSmall.States

/-! Walk chunk 1220, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1220 : RSBounds.HelfgottSmall.ChunkGood 1220 := by
  decide +kernel
