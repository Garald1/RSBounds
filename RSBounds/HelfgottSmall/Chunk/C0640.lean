import RSBounds.HelfgottSmall.States

/-! Walk chunk 640, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_640 : RSBounds.HelfgottSmall.ChunkGood 640 := by
  decide +kernel
