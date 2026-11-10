# Quadratic smoothing checkpoint

This is a source-preparation checkpoint, not a verification claim. None of
the ten modules below has yet been compiled or axiom-audited. The signed-tail
endpoint module is now checked; its dependent signed-tail assembly retains
compiler priority over these first checks.

| Source | Prepared scope |
|---|---|
| `RSBounds/QuadraticMellin.lean` | `(1-u)_+^2/2` and Mellin kernel `1/[s(s+1)(s+2)]`. |
| `RSBounds/QuadraticKernel.lean` | Holomorphic numerator, `DecayTwo`, and existing-contour specialization. |
| `RSBounds/QuadraticPsi.lean` | Finite psi smoothing, second-difference identity, unsmoothing cost `h`. |
| `RSBounds/QuadraticPsiMellin.lean` | Exact identification of the Mellin prime sum with `Psi2`. |
| `RSBounds/QuadraticZetaFormula.lean` | Actual-zeta formula for `Psi2`, retaining the left integral. |
| `RSBounds/QuadraticZeroKernel.lean` | Dimensionless near/far coefficient bounds at `m=2`. |
| `RSBounds/QuadraticKernelScaling.lean` | Actual physical coefficient and exact dilation identities. |
| `RSBounds/QuadraticLowerKernel.lean` | Lower-average near/far bounds with the same common constants. |
| `RSBounds/QuadraticCoefficientBounds.lean` | Actual upper/lower coefficients bounded using `abs gamma` and `abs gamma^3`. |
| `RSBounds/QuadraticAveragedFormula.lean` | Actual averaged formula along common good heights, retaining the left integral. |

The source order is Mellin, Psi, PsiMellin, Kernel, ZeroKernel, ZetaFormula;
the zeta-formula module needs both the kernel and prime-sum branches. Scaling
and LowerKernel follow ZeroKernel; CoefficientBounds follows those two. The contour
argument is reused from the checked `QuadraticContourLimit` and
`QuadraticSubOne` modules. The generic iterated integral, differentiation,
and affine norm estimates in `PolynomialZeroKernel` are reused at `n=2`.

The averaged formula follows ZetaFormula and KernelScaling. Further work
is needed for a quantitative averaged left-remainder estimate and numerical
assembly, as well as checking all prepared sources. The intended
near coefficient is `(1+delta)*x^beta/|gamma|`; the far coefficient uses
`R2(delta)=((1+delta)^3+1)^2` divided by `delta^2*|gamma|^3`.

The separate numerical worker owns reflection averaging under
`rho -> 1-conj(rho)` and the transfer to positive-ordinate zero counts.
That pairing is essential to retain the paper's half-count factor; simply
doubling a uniform positive-height bound is not the intended theorem.
