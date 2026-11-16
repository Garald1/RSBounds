import RSBounds.HelfgottSmall.States

/-! Walk chunk 680, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_680 : RSBounds.HelfgottSmall.ChunkGood 680 := by
  decide +kernel
