import RSBounds.HelfgottSmall.States

/-! Walk chunk 223, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_223 : RSBounds.HelfgottSmall.ChunkGood 223 := by
  decide +kernel
