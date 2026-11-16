import RSBounds.HelfgottSmall.States

/-! Walk chunk 933, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_933 : RSBounds.HelfgottSmall.ChunkGood 933 := by
  decide +kernel
