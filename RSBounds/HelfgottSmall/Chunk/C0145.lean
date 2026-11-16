import RSBounds.HelfgottSmall.States

/-! Walk chunk 145, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_145 : RSBounds.HelfgottSmall.ChunkGood 145 := by
  decide +kernel
