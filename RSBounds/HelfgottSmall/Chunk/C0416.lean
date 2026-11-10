import RSBounds.HelfgottSmall.States

/-! Walk chunk 416, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_416 : RSBounds.HelfgottSmall.ChunkGood 416 := by
  decide +kernel
