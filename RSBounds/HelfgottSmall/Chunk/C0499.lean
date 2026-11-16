import RSBounds.HelfgottSmall.States

/-! Walk chunk 499, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_499 : RSBounds.HelfgottSmall.ChunkGood 499 := by
  decide +kernel
