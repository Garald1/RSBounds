import RSBounds.HelfgottSmall.States

/-! Walk chunk 509, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_509 : RSBounds.HelfgottSmall.ChunkGood 509 := by
  decide +kernel
