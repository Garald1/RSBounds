import RSBounds.HelfgottSmall.States

/-! Walk chunk 350, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_350 : RSBounds.HelfgottSmall.ChunkGood 350 := by
  decide +kernel
