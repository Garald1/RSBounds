import RSBounds.HelfgottSmall.States

/-! Walk chunk 421, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_421 : RSBounds.HelfgottSmall.ChunkGood 421 := by
  decide +kernel
