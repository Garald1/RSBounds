import RSBounds.HelfgottSmall.States

/-! Walk chunk 510, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_510 : RSBounds.HelfgottSmall.ChunkGood 510 := by
  decide +kernel
