import RSBounds.HelfgottSmall.States

/-! Walk chunk 902, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_902 : RSBounds.HelfgottSmall.ChunkGood 902 := by
  decide +kernel
