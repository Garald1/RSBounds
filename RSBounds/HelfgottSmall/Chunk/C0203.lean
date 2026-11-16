import RSBounds.HelfgottSmall.States

/-! Walk chunk 203, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_203 : RSBounds.HelfgottSmall.ChunkGood 203 := by
  decide +kernel
