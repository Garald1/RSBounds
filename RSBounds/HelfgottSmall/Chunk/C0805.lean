import RSBounds.HelfgottSmall.States

/-! Walk chunk 805, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_805 : RSBounds.HelfgottSmall.ChunkGood 805 := by
  decide +kernel
