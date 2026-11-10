import RSBounds.HelfgottSmall.States

/-! Walk chunk 720, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_720 : RSBounds.HelfgottSmall.ChunkGood 720 := by
  decide +kernel
