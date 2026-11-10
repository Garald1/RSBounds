import RSBounds.HelfgottSmall.States

/-! Walk chunk 1201, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1201 : RSBounds.HelfgottSmall.ChunkGood 1201 := by
  decide +kernel
