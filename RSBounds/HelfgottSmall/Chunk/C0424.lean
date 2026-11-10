import RSBounds.HelfgottSmall.States

/-! Walk chunk 424, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_424 : RSBounds.HelfgottSmall.ChunkGood 424 := by
  decide +kernel
