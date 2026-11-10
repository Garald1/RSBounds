import RSBounds.HelfgottSmall.States

/-! Walk chunk 835, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_835 : RSBounds.HelfgottSmall.ChunkGood 835 := by
  decide +kernel
