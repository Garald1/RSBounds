import RSBounds.HelfgottSmall.States

/-! Walk chunk 404, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_404 : RSBounds.HelfgottSmall.ChunkGood 404 := by
  decide +kernel
