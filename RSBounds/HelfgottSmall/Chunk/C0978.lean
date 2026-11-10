import RSBounds.HelfgottSmall.States

/-! Walk chunk 978, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_978 : RSBounds.HelfgottSmall.ChunkGood 978 := by
  decide +kernel
