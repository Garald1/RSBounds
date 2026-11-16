import RSBounds.HelfgottSmall.States

/-! Walk chunk 204, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_204 : RSBounds.HelfgottSmall.ChunkGood 204 := by
  decide +kernel
