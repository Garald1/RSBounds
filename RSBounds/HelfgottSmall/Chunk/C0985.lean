import RSBounds.HelfgottSmall.States

/-! Walk chunk 985, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_985 : RSBounds.HelfgottSmall.ChunkGood 985 := by
  decide +kernel
