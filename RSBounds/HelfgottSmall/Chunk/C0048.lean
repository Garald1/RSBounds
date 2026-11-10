import RSBounds.HelfgottSmall.States

/-! Walk chunk 48, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_48 : RSBounds.HelfgottSmall.ChunkGood 48 := by
  decide +kernel
