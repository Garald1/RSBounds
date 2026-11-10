import RSBounds.HelfgottSmall.States

/-! Walk chunk 65, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_65 : RSBounds.HelfgottSmall.ChunkGood 65 := by
  decide +kernel
