import RSBounds.HelfgottSmall.States

/-! Walk chunk 192, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_192 : RSBounds.HelfgottSmall.ChunkGood 192 := by
  decide +kernel
