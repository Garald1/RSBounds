import RSBounds.HelfgottSmall.States

/-! Walk chunk 422, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_422 : RSBounds.HelfgottSmall.ChunkGood 422 := by
  decide +kernel
