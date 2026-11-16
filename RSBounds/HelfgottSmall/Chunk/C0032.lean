import RSBounds.HelfgottSmall.States

/-! Walk chunk 32, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_32 : RSBounds.HelfgottSmall.ChunkGood 32 := by
  decide +kernel
