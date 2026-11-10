import RSBounds.HelfgottSmall.States

/-! Walk chunk 608, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_608 : RSBounds.HelfgottSmall.ChunkGood 608 := by
  decide +kernel
