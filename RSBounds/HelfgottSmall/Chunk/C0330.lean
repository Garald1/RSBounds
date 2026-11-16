import RSBounds.HelfgottSmall.States

/-! Walk chunk 330, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_330 : RSBounds.HelfgottSmall.ChunkGood 330 := by
  decide +kernel
