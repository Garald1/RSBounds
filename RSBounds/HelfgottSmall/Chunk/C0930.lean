import RSBounds.HelfgottSmall.States

/-! Walk chunk 930, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_930 : RSBounds.HelfgottSmall.ChunkGood 930 := by
  decide +kernel
