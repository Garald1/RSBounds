import RSBounds.HelfgottSmall.States

/-! Walk chunk 866, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_866 : RSBounds.HelfgottSmall.ChunkGood 866 := by
  decide +kernel
