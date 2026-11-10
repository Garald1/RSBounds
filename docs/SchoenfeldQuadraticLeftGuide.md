# Actual quadratic left-contour allowance

Status: source prepared, not compiled or axiom-audited. The consolidated
quadratic kernel and psi modules must pass before this module is checked.
Earlier drafts and checked predecessor sources remain unchanged.

The main proposed export in `RSBounds/SchoenfeldQuadraticLeft.lean` is
`SchoenfeldQuadraticLeft.leftAllowance_le`: for `x > 0`, `delta > 0`,
and `2 * delta < 1`, the maximum of the actual upper and lower averaged
left remainders is at most

\[
\frac{150000}{\delta^2\sqrt{x}}.
\]

The proof uses the quadratic kernel's left-line majorant
`27 / (1 + |t|)^3`, the already checked actual zeta logarithmic-derivative
bound `500 * (1 + |t|)^(1/2)`, and the already checked integral
`integral (1 + |t|)^(-3/2) = 4`. No new contour theorem or assumed integral
constant is introduced. The resulting primitive bound is
`norm (psi2LeftRemainder y) ≤ 9000 * y * sqrt y`.

All three arguments of the upper or lower finite difference lie in
`(0, 2*x]`. Thus each primitive term is at most `36000 * x * sqrt x`.
The triangle weights `1,2,1` give coefficient 144000, relaxed to 150000
after dividing by `(delta*x)^2`.

The proposed `psi_error_le_envelope` corollary replaces the actual left
allowance in the consolidated psi theorem with this numerical bound. Its
only zero-location premise is the explicit `Goals.FiniteRH 1894439`;
the existing near/far cutoff conditions remain explicit. The original
Schoenfeld scalar parameter balance is a separate obligation.

After sourcing `../lean-env.sh`, the prepared verification command is
`python verification/run_schoenfeld_quadratic_left_check.py`. It will
compile the exact source and seven transitive axiom queries in one
process. Intended receipt:
`verification/schoenfeld-quadratic-left-run.json`.
