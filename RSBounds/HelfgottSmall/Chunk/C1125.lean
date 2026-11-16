import RSBounds.HelfgottSmall.States

/-! Walk chunk 1125, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1125 : RSBounds.HelfgottSmall.ChunkGood 1125 := by
  decide +kernel
