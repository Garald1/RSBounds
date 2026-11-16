import RSBounds.HelfgottSmall.States

/-! Walk chunk 560, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_560 : RSBounds.HelfgottSmall.ChunkGood 560 := by
  decide +kernel
