import RSBounds.HelfgottSmall.States

/-! Walk chunk 121, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_121 : RSBounds.HelfgottSmall.ChunkGood 121 := by
  decide +kernel
