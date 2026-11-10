import RSBounds.HelfgottSmall.States

/-! Walk chunk 666, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_666 : RSBounds.HelfgottSmall.ChunkGood 666 := by
  decide +kernel
