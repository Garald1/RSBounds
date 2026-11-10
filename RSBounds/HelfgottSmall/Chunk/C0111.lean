import RSBounds.HelfgottSmall.States

/-! Walk chunk 111, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_111 : RSBounds.HelfgottSmall.ChunkGood 111 := by
  decide +kernel
