import RSBounds.HelfgottSmall.States

/-! Walk chunk 1123, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1123 : RSBounds.HelfgottSmall.ChunkGood 1123 := by
  decide +kernel
