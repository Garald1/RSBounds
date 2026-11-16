import RSBounds.HelfgottSmall.States

/-! Walk chunk 650, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_650 : RSBounds.HelfgottSmall.ChunkGood 650 := by
  decide +kernel
