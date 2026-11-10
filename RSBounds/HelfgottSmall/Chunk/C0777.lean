import RSBounds.HelfgottSmall.States

/-! Walk chunk 777, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_777 : RSBounds.HelfgottSmall.ChunkGood 777 := by
  decide +kernel
