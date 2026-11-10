import RSBounds.HelfgottSmall.States

/-! Walk chunk 212, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_212 : RSBounds.HelfgottSmall.ChunkGood 212 := by
  decide +kernel
