import RSBounds.HelfgottSmall.States

/-! Walk chunk 33, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_33 : RSBounds.HelfgottSmall.ChunkGood 33 := by
  decide +kernel
