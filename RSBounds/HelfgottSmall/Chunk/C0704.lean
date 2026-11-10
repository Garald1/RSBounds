import RSBounds.HelfgottSmall.States

/-! Walk chunk 704, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_704 : RSBounds.HelfgottSmall.ChunkGood 704 := by
  decide +kernel
