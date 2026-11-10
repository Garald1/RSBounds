import RSBounds.HelfgottSmall.States

/-! Walk chunk 256, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_256 : RSBounds.HelfgottSmall.ChunkGood 256 := by
  decide +kernel
