# Theta-chain diagnostic (not part of the proof)

The three files were removed from the project on 2026-11-08; this records why
they did not compile.

`PsiFiniteRH`, `PsiFiniteRHZeroFree` and `ThetaLarge` cannot be built: the pinned
TernaryGoldbach lemmas used by `PsiFiniteRH` require `[Fact TernaryGoldbach.RHUpTo]`
(RH up to 3e10). To see whether the height edits introduce errors, scratch copies of
the three files were compiled with one added line after the namespace,
`variable [Fact TernaryGoldbach.RHUpTo]`, once for the edited sources and once for the
baseline sources (with the baseline `Theta`). These copies were never shipped.

* `PsiFiniteRHZeroFree-edited-with-instance.out`: the edited file elaborates (exit 0;
  warnings only).
* `ThetaLarge-edited-with-instance.out` and `ThetaLarge-baseline-with-instance.out`:
  7 errors each, at identical locations (lines 27, 66, 92, 172, 180, 182, 343).
