import RSBounds.HelfgottSmall.States

/-! Walk chunk 620, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_620 : RSBounds.HelfgottSmall.ChunkGood 620 := by
  decide +kernel
