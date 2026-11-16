import RSBounds.HelfgottSmall.States

/-! Walk chunk 386, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_386 : RSBounds.HelfgottSmall.ChunkGood 386 := by
  decide +kernel
