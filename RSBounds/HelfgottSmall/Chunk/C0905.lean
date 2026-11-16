import RSBounds.HelfgottSmall.States

/-! Walk chunk 905, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_905 : RSBounds.HelfgottSmall.ChunkGood 905 := by
  decide +kernel
