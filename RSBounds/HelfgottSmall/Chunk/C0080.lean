import RSBounds.HelfgottSmall.States

/-! Walk chunk 80, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_80 : RSBounds.HelfgottSmall.ChunkGood 80 := by
  decide +kernel
