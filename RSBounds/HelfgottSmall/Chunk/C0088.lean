import RSBounds.HelfgottSmall.States

/-! Walk chunk 88, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_88 : RSBounds.HelfgottSmall.ChunkGood 88 := by
  decide +kernel
