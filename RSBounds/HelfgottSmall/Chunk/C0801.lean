import RSBounds.HelfgottSmall.States

/-! Walk chunk 801, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_801 : RSBounds.HelfgottSmall.ChunkGood 801 := by
  decide +kernel
