import RSBounds.HelfgottSmall.States

/-! Walk chunk 830, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_830 : RSBounds.HelfgottSmall.ChunkGood 830 := by
  decide +kernel
