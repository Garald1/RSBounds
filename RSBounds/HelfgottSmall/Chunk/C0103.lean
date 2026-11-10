import RSBounds.HelfgottSmall.States

/-! Walk chunk 103, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_103 : RSBounds.HelfgottSmall.ChunkGood 103 := by
  decide +kernel
