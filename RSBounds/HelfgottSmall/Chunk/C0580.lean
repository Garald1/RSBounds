import RSBounds.HelfgottSmall.States

/-! Walk chunk 580, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_580 : RSBounds.HelfgottSmall.ChunkGood 580 := by
  decide +kernel
