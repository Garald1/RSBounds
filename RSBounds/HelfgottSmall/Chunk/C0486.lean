import RSBounds.HelfgottSmall.States

/-! Walk chunk 486, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_486 : RSBounds.HelfgottSmall.ChunkGood 486 := by
  decide +kernel
