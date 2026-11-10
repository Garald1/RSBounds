import RSBounds.HelfgottSmall.States

/-! Walk chunk 129, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_129 : RSBounds.HelfgottSmall.ChunkGood 129 := by
  decide +kernel
