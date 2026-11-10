import RSBounds.HelfgottSmall.States

/-! Walk chunk 83, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_83 : RSBounds.HelfgottSmall.ChunkGood 83 := by
  decide +kernel
