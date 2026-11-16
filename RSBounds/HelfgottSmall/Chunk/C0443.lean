import RSBounds.HelfgottSmall.States

/-! Walk chunk 443, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_443 : RSBounds.HelfgottSmall.ChunkGood 443 := by
  decide +kernel
