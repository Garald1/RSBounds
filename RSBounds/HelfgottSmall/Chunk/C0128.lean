import RSBounds.HelfgottSmall.States

/-! Walk chunk 128, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_128 : RSBounds.HelfgottSmall.ChunkGood 128 := by
  decide +kernel
