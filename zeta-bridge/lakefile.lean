import Lake
open Lake DSL

/-!
A separate Lake project, so that building RSBounds itself does not fetch `zeta`.

It needs only `RSBounds.Targets` (Mathlib-only definitions) from RSBounds, and
`Zeta.Main` from S. Mercuri and B. Mehta's `smmercuri/zeta` at the tag of its prebuilt
release for RH up to height 1895609. Both use Lean v4.35.0 and Mathlib `56a005855`.
-/

package ZetaBridge

require RSBounds from "../"

require Zeta from git "https://github.com/smmercuri/zeta" @ "v1-1.8956e6"

@[default_target] lean_lib ZetaBridge where
  roots := #[`ZetaBridge]
