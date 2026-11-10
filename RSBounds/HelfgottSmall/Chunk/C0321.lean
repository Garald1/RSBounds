import RSBounds.HelfgottSmall.States

/-! Walk chunk 321, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_321 : RSBounds.HelfgottSmall.ChunkGood 321 := by
  decide +kernel
