import RSBounds.HelfgottSmall.States

/-! Walk chunk 201, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_201 : RSBounds.HelfgottSmall.ChunkGood 201 := by
  decide +kernel
