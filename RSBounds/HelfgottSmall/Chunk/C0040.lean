import RSBounds.HelfgottSmall.States

/-! Walk chunk 40, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_40 : RSBounds.HelfgottSmall.ChunkGood 40 := by
  decide +kernel
