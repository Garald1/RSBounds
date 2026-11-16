import RSBounds.HelfgottSmall.States

/-! Walk chunk 440, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_440 : RSBounds.HelfgottSmall.ChunkGood 440 := by
  decide +kernel
