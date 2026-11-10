import RSBounds.HelfgottSmall.States

/-! Walk chunk 1128, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1128 : RSBounds.HelfgottSmall.ChunkGood 1128 := by
  decide +kernel
