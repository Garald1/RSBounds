import RSBounds.HelfgottSmall.States

/-! Walk chunk 270, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_270 : RSBounds.HelfgottSmall.ChunkGood 270 := by
  decide +kernel
