import RSBounds.HelfgottSmall.States

/-! Walk chunk 602, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_602 : RSBounds.HelfgottSmall.ChunkGood 602 := by
  decide +kernel
