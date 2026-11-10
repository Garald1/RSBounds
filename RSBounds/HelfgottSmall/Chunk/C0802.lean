import RSBounds.HelfgottSmall.States

/-! Walk chunk 802, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_802 : RSBounds.HelfgottSmall.ChunkGood 802 := by
  decide +kernel
