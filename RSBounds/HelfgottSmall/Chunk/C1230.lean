import RSBounds.HelfgottSmall.States

/-! Walk chunk 1230, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1230 : RSBounds.HelfgottSmall.ChunkGood 1230 := by
  decide +kernel
