import RSBounds.HelfgottSmall.States

/-! Walk chunk 302, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_302 : RSBounds.HelfgottSmall.ChunkGood 302 := by
  decide +kernel
