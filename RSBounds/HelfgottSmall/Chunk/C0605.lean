import RSBounds.HelfgottSmall.States

/-! Walk chunk 605, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_605 : RSBounds.HelfgottSmall.ChunkGood 605 := by
  decide +kernel
