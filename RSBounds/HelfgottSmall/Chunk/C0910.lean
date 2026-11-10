import RSBounds.HelfgottSmall.States

/-! Walk chunk 910, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_910 : RSBounds.HelfgottSmall.ChunkGood 910 := by
  decide +kernel
