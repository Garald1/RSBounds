import RSBounds.HelfgottSmall.States

/-! Walk chunk 460, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_460 : RSBounds.HelfgottSmall.ChunkGood 460 := by
  decide +kernel
