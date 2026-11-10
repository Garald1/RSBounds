import RSBounds.HelfgottSmall.States

/-! Walk chunk 90, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_90 : RSBounds.HelfgottSmall.ChunkGood 90 := by
  decide +kernel
