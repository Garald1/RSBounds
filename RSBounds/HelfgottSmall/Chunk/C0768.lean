import RSBounds.HelfgottSmall.States

/-! Walk chunk 768, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_768 : RSBounds.HelfgottSmall.ChunkGood 768 := by
  decide +kernel
