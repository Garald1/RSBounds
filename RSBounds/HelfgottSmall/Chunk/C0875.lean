import RSBounds.HelfgottSmall.States

/-! Walk chunk 875, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_875 : RSBounds.HelfgottSmall.ChunkGood 875 := by
  decide +kernel
