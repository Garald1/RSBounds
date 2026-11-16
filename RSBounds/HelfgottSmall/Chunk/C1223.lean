import RSBounds.HelfgottSmall.States

/-! Walk chunk 1223, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1223 : RSBounds.HelfgottSmall.ChunkGood 1223 := by
  decide +kernel
