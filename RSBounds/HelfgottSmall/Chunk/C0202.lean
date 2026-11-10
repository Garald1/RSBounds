import RSBounds.HelfgottSmall.States

/-! Walk chunk 202, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_202 : RSBounds.HelfgottSmall.ChunkGood 202 := by
  decide +kernel
