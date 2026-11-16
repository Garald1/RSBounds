import RSBounds.HelfgottSmall.States

/-! Walk chunk 784, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_784 : RSBounds.HelfgottSmall.ChunkGood 784 := by
  decide +kernel
