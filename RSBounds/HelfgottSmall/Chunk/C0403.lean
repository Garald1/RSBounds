import RSBounds.HelfgottSmall.States

/-! Walk chunk 403, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_403 : RSBounds.HelfgottSmall.ChunkGood 403 := by
  decide +kernel
