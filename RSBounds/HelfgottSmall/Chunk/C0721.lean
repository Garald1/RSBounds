import RSBounds.HelfgottSmall.States

/-! Walk chunk 721, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_721 : RSBounds.HelfgottSmall.ChunkGood 721 := by
  decide +kernel
