import RSBounds.HelfgottSmall.States

/-! Walk chunk 425, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_425 : RSBounds.HelfgottSmall.ChunkGood 425 := by
  decide +kernel
