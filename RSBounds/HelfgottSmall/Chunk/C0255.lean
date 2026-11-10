import RSBounds.HelfgottSmall.States

/-! Walk chunk 255, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_255 : RSBounds.HelfgottSmall.ChunkGood 255 := by
  decide +kernel
