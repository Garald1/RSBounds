import RSBounds.HelfgottSmall.States

/-! Walk chunk 144, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_144 : RSBounds.HelfgottSmall.ChunkGood 144 := by
  decide +kernel
