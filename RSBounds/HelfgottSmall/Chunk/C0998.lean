import RSBounds.HelfgottSmall.States

/-! Walk chunk 998, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_998 : RSBounds.HelfgottSmall.ChunkGood 998 := by
  decide +kernel
