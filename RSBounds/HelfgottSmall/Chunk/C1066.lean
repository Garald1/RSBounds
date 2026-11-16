import RSBounds.HelfgottSmall.States

/-! Walk chunk 1066, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1066 : RSBounds.HelfgottSmall.ChunkGood 1066 := by
  decide +kernel
