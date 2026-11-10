import RSBounds.HelfgottSmall.States

/-! Walk chunk 890, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_890 : RSBounds.HelfgottSmall.ChunkGood 890 := by
  decide +kernel
