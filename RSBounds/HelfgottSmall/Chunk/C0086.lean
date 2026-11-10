import RSBounds.HelfgottSmall.States

/-! Walk chunk 86, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_86 : RSBounds.HelfgottSmall.ChunkGood 86 := by
  decide +kernel
