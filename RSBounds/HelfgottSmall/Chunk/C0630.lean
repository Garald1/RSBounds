import RSBounds.HelfgottSmall.States

/-! Walk chunk 630, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_630 : RSBounds.HelfgottSmall.ChunkGood 630 := by
  decide +kernel
