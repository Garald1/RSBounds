import RSBounds.HelfgottSmall.States

/-! Walk chunk 625, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_625 : RSBounds.HelfgottSmall.ChunkGood 625 := by
  decide +kernel
