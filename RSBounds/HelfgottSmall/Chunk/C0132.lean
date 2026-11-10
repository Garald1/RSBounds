import RSBounds.HelfgottSmall.States

/-! Walk chunk 132, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_132 : RSBounds.HelfgottSmall.ChunkGood 132 := by
  decide +kernel
