import RSBounds.HelfgottSmall.States

/-! Walk chunk 1015, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1015 : RSBounds.HelfgottSmall.ChunkGood 1015 := by
  decide +kernel
