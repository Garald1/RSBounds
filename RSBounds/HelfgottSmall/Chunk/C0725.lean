import RSBounds.HelfgottSmall.States

/-! Walk chunk 725, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_725 : RSBounds.HelfgottSmall.ChunkGood 725 := by
  decide +kernel
