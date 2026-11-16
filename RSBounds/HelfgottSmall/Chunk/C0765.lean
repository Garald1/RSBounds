import RSBounds.HelfgottSmall.States

/-! Walk chunk 765, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_765 : RSBounds.HelfgottSmall.ChunkGood 765 := by
  decide +kernel
