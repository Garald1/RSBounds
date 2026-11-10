# Header snapshots: an unadopted development optimization

**No incremental snapshot has been generated or used in this project's
verification chain.** The ordinary source/import checks and independent
Comparator path remain unchanged. This is a read-only implementation audit
for possible future development use, not a verification receipt.

The inspected implementation is the installed Lean 4.35.0 source, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Exact source hashes are in
[`lean-header-cache-source-audit.json`](../verification/lean-header-cache-source-audit.json).

## What Lean does

`--incr-header-save` saves the post-import state. `truncateToHeader` discards
all command bodies, so subsequent proof edits are re-elaborated rather than
loaded as already proved commands
([`Lean/Language/Lean.lean`, lines 819–852](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Language/Lean.lean#L819)).

On reload, Lean reparses the import header and compares its syntax with the
saved header, ignoring trailing whitespace. Matching syntax reuses the old
command state; a changed header follows ordinary import processing
([same file, lines 394–488](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Language/Lean.lean#L394)).

That is **not dependency-content invalidation**. The snapshot `.deps` file
contains `ModuleArtifacts`, whose fields are paths, not content hashes
([`Lean/Setup.lean`, lines 112–141](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Setup.lean#L112)).
The inspected loader rereads those regions and the saved environment without
comparing their content or modification times with the snapshot's creation
state ([`Lean/Elab/Frontend.lean`, lines 190–230](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Elab/Frontend.lean#L190)).
Low-level artifact-format checks are not a substitute for that comparison.

## Required external guard before any future reuse

A cache wrapper would have to record and validate all of the following:

- The exact import header and identical CLI, trust-level, setup, and option
  configuration. The built-in reuse path skips fresh header setup.
- Every transitive artifact named in `.deps`, including the relevant
  `.olean`, `.olean.server`, `.olean.private`, `.ir.sig`, and `.ir` files,
  using content hashes. Dependencies must not be rewritten during reuse.
- The snapshot and `.deps` contents themselves, plus the pinned toolchain,
  executable, dependent libraries, and loaded plugins.
- Ordinary fresh imports whenever any check fails.

The executable/library condition is explicit: closure-bearing compacted
snapshots require identical executables **and dependent libraries**
([`Lean/CompactedRegion.lean`, lines 83–87](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/CompactedRegion.lean#L83)).
The frontend also reruns initializers and explicitly records a possible
theoretical divergence for unusual initializers
([`Lean/Elab/Frontend.lean`, lines 321–335](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Elab/Frontend.lean#L321)).

These features therefore merit a separately tested, guarded **local
development cache**, not an unqualified replacement for the project's
ordinary verification and independent kernel replay. No speedup measurement
or blanket safety claim is made here.
