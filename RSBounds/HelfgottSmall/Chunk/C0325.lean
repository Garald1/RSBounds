import RSBounds.HelfgottSmall.States

/-! Walk chunk 325, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_325 : RSBounds.HelfgottSmall.ChunkGood 325 := by
  decide +kernel
