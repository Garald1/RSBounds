import RSBounds.HelfgottSmall.States

/-! Walk chunk 231, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_231 : RSBounds.HelfgottSmall.ChunkGood 231 := by
  decide +kernel
