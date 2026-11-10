import RSBounds.HelfgottSmall.States

/-! Walk chunk 239, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_239 : RSBounds.HelfgottSmall.ChunkGood 239 := by
  decide +kernel
