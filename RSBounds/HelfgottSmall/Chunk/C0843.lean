import RSBounds.HelfgottSmall.States

/-! Walk chunk 843, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_843 : RSBounds.HelfgottSmall.ChunkGood 843 := by
  decide +kernel
