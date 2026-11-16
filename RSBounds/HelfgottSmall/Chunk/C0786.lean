import RSBounds.HelfgottSmall.States

/-! Walk chunk 786, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_786 : RSBounds.HelfgottSmall.ChunkGood 786 := by
  decide +kernel
