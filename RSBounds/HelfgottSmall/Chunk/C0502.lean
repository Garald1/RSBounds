import RSBounds.HelfgottSmall.States

/-! Walk chunk 502, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_502 : RSBounds.HelfgottSmall.ChunkGood 502 := by
  decide +kernel
