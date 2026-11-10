import RSBounds.HelfgottSmall.States

/-! Walk chunk 68, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_68 : RSBounds.HelfgottSmall.ChunkGood 68 := by
  decide +kernel
