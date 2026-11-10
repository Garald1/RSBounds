import RSBounds.HelfgottSmall.States

/-! Walk chunk 785, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_785 : RSBounds.HelfgottSmall.ChunkGood 785 := by
  decide +kernel
