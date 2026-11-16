import RSBounds.HelfgottSmall.States

/-! Walk chunk 730, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_730 : RSBounds.HelfgottSmall.ChunkGood 730 := by
  decide +kernel
