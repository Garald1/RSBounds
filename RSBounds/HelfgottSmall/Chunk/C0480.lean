import RSBounds.HelfgottSmall.States

/-! Walk chunk 480, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_480 : RSBounds.HelfgottSmall.ChunkGood 480 := by
  decide +kernel
