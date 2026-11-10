import RSBounds.HelfgottSmall.States

/-! Walk chunk 1101, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1101 : RSBounds.HelfgottSmall.ChunkGood 1101 := by
  decide +kernel
