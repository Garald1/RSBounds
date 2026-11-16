import RSBounds.HelfgottSmall.States

/-! Walk chunk 576, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_576 : RSBounds.HelfgottSmall.ChunkGood 576 := by
  decide +kernel
