import RSBounds.HelfgottSmall.States

/-! Walk chunk 135, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_135 : RSBounds.HelfgottSmall.ChunkGood 135 := by
  decide +kernel
