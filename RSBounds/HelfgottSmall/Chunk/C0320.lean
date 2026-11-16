import RSBounds.HelfgottSmall.States

/-! Walk chunk 320, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_320 : RSBounds.HelfgottSmall.ChunkGood 320 := by
  decide +kernel
