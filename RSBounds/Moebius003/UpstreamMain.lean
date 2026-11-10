/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Upstream
import TernaryGoldbach.MainTheorems

/-!
# Upstream's main theorems without `RamareMoebius`

`TernaryGoldbach.ternary_goldbach_of_hypotheses` and `ternary_goldbach_large_of_hypotheses`
(calr3/ternary-goldbach at `192ca57`) with `hμ` supplied by `ramareMoebius_of_plattGRH`. This module
imports all of upstream's development, including its kernel sieve, which upstream reports at
7.5 GB of memory.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open TernaryGoldbach

/-- **Ternary Goldbach from two hypotheses**: `PlattGRH` and `BinaryGoldbachInput`. -/
theorem ternary_goldbach_of_two_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput) :
    Statement :=
  ternary_goldbach_of_hypotheses hGRH hBG (ramareMoebius_of_plattGRH hGRH)

/-- Every odd `n ≥ 10²⁷` is a sum of three primes, given `PlattGRH`. -/
theorem ternary_goldbach_large_of_plattGRH (hGRH : PlattGRH) : TernaryGoldbachFrom (10 ^ 27) :=
  ternary_goldbach_large_of_hypotheses hGRH (ramareMoebius_of_plattGRH hGRH)

end TernaryGoldbach.RSBounds.Moebius003
