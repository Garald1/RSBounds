import RSBounds.HelfgottSmall.States

/-! Walk chunk 525, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_525 : RSBounds.HelfgottSmall.ChunkGood 525 := by
  decide +kernel
