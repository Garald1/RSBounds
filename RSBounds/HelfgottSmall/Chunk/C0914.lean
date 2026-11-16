import RSBounds.HelfgottSmall.States

/-! Walk chunk 914, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_914 : RSBounds.HelfgottSmall.ChunkGood 914 := by
  decide +kernel
