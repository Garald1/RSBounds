import RSBounds.HelfgottSmall.States

/-! Walk chunk 200, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_200 : RSBounds.HelfgottSmall.ChunkGood 200 := by
  decide +kernel
