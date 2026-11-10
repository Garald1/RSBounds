import RSBounds.HelfgottSmall.States

/-! Walk chunk 409, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_409 : RSBounds.HelfgottSmall.ChunkGood 409 := by
  decide +kernel
