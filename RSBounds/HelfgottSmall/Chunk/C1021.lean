import RSBounds.HelfgottSmall.States

/-! Walk chunk 1021, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1021 : RSBounds.HelfgottSmall.ChunkGood 1021 := by
  decide +kernel
