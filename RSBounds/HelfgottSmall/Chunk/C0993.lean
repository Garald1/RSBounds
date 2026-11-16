import RSBounds.HelfgottSmall.States

/-! Walk chunk 993, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_993 : RSBounds.HelfgottSmall.ChunkGood 993 := by
  decide +kernel
