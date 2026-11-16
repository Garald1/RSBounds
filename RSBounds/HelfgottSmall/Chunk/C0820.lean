import RSBounds.HelfgottSmall.States

/-! Walk chunk 820, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_820 : RSBounds.HelfgottSmall.ChunkGood 820 := by
  decide +kernel
