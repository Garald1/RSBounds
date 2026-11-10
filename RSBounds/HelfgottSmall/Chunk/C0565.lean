import RSBounds.HelfgottSmall.States

/-! Walk chunk 565, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_565 : RSBounds.HelfgottSmall.ChunkGood 565 := by
  decide +kernel
