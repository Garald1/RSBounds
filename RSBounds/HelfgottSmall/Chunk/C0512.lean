import RSBounds.HelfgottSmall.States

/-! Walk chunk 512, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_512 : RSBounds.HelfgottSmall.ChunkGood 512 := by
  decide +kernel
