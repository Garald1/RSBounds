import RSBounds.HelfgottSmall.States

/-! Walk chunk 224, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_224 : RSBounds.HelfgottSmall.ChunkGood 224 := by
  decide +kernel
