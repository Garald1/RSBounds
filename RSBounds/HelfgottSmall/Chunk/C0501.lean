import RSBounds.HelfgottSmall.States

/-! Walk chunk 501, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_501 : RSBounds.HelfgottSmall.ChunkGood 501 := by
  decide +kernel
