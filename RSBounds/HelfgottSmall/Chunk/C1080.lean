import RSBounds.HelfgottSmall.States

/-! Walk chunk 1080, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1080 : RSBounds.HelfgottSmall.ChunkGood 1080 := by
  decide +kernel
