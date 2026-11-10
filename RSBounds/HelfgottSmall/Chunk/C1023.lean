import RSBounds.HelfgottSmall.States

/-! Walk chunk 1023, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1023 : RSBounds.HelfgottSmall.ChunkGood 1023 := by
  decide +kernel
