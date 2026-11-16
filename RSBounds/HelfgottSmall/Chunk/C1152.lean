import RSBounds.HelfgottSmall.States

/-! Walk chunk 1152, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1152 : RSBounds.HelfgottSmall.ChunkGood 1152 := by
  decide +kernel
