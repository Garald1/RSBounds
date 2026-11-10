import RSBounds.HelfgottSmall.States

/-! Walk chunk 825, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_825 : RSBounds.HelfgottSmall.ChunkGood 825 := by
  decide +kernel
