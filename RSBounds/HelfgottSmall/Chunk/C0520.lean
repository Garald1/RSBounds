import RSBounds.HelfgottSmall.States

/-! Walk chunk 520, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_520 : RSBounds.HelfgottSmall.ChunkGood 520 := by
  decide +kernel
