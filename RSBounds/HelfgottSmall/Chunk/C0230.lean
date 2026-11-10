import RSBounds.HelfgottSmall.States

/-! Walk chunk 230, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_230 : RSBounds.HelfgottSmall.ChunkGood 230 := by
  decide +kernel
