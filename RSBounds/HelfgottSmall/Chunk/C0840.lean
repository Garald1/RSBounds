import RSBounds.HelfgottSmall.States

/-! Walk chunk 840, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_840 : RSBounds.HelfgottSmall.ChunkGood 840 := by
  decide +kernel
