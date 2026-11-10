import RSBounds.HelfgottSmall.States

/-! Walk chunk 370, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_370 : RSBounds.HelfgottSmall.ChunkGood 370 := by
  decide +kernel
