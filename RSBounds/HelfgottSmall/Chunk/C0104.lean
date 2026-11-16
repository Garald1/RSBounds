import RSBounds.HelfgottSmall.States

/-! Walk chunk 104, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_104 : RSBounds.HelfgottSmall.ChunkGood 104 := by
  decide +kernel
