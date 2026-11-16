import RSBounds.HelfgottSmall.States

/-! Walk chunk 700, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_700 : RSBounds.HelfgottSmall.ChunkGood 700 := by
  decide +kernel
