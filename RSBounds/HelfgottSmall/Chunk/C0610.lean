import RSBounds.HelfgottSmall.States

/-! Walk chunk 610, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_610 : RSBounds.HelfgottSmall.ChunkGood 610 := by
  decide +kernel
