import RSBounds.HelfgottSmall.States

/-! Walk chunk 412, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_412 : RSBounds.HelfgottSmall.ChunkGood 412 := by
  decide +kernel
