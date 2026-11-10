import RSBounds.HelfgottSmall.States

/-! Walk chunk 445, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_445 : RSBounds.HelfgottSmall.ChunkGood 445 := by
  decide +kernel
