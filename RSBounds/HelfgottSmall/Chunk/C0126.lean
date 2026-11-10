import RSBounds.HelfgottSmall.States

/-! Walk chunk 126, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_126 : RSBounds.HelfgottSmall.ChunkGood 126 := by
  decide +kernel
