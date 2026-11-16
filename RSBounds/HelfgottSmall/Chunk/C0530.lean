import RSBounds.HelfgottSmall.States

/-! Walk chunk 530, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_530 : RSBounds.HelfgottSmall.ChunkGood 530 := by
  decide +kernel
