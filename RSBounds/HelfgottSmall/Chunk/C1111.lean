import RSBounds.HelfgottSmall.States

/-! Walk chunk 1111, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1111 : RSBounds.HelfgottSmall.ChunkGood 1111 := by
  decide +kernel
