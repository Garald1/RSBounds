import RSBounds.HelfgottSmall.States

/-! Walk chunk 384, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_384 : RSBounds.HelfgottSmall.ChunkGood 384 := by
  decide +kernel
