import RSBounds.HelfgottSmall.States

/-! Walk chunk 288, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_288 : RSBounds.HelfgottSmall.ChunkGood 288 := by
  decide +kernel
