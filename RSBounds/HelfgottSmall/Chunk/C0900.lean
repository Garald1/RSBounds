import RSBounds.HelfgottSmall.States

/-! Walk chunk 900, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_900 : RSBounds.HelfgottSmall.ChunkGood 900 := by
  decide +kernel
