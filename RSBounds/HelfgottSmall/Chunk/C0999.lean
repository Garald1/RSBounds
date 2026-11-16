import RSBounds.HelfgottSmall.States

/-! Walk chunk 999, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_999 : RSBounds.HelfgottSmall.ChunkGood 999 := by
  decide +kernel
