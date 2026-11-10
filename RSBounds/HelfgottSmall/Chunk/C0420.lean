import RSBounds.HelfgottSmall.States

/-! Walk chunk 420, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_420 : RSBounds.HelfgottSmall.ChunkGood 420 := by
  decide +kernel
