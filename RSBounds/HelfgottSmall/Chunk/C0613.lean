import RSBounds.HelfgottSmall.States

/-! Walk chunk 613, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_613 : RSBounds.HelfgottSmall.ChunkGood 613 := by
  decide +kernel
