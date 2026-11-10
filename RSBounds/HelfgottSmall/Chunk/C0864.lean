import RSBounds.HelfgottSmall.States

/-! Walk chunk 864, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_864 : RSBounds.HelfgottSmall.ChunkGood 864 := by
  decide +kernel
