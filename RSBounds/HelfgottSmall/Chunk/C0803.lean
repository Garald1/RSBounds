import RSBounds.HelfgottSmall.States

/-! Walk chunk 803, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_803 : RSBounds.HelfgottSmall.ChunkGood 803 := by
  decide +kernel
