/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.CommonRoots
public import ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivatives

/-!
# Corollary 6.2 (common roots)

`ArithmeticOfJacobiPolynomials.commonRootsStatement` proves `CommonRootsStatement`, combining
`commonRootsStatement_of_irreducible` with Theorem 1.5 (`legendreAndDerivativesStatement`).
Conditional on the computed inputs `FirstDerivativeIntegerInequalities` and
`FirstDerivativeFactorDegreeChecks` (`ComputerVerified`) and on `DengLegendreIrreducibility`
([Deng, Theorem 1.1]), `HansonLcmBound` ([Hanson, Theorem 1]),
the proved `intervalVandermondeBound` (Lemma 2.5) and
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]).
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Corollary 6.2.** (1) For distinct nonnegative integers `a, b`, only finitely many pairs
of different degrees give Jacobi polynomials `P_n^{(a,b)}` with a common complex root.
(2) No two distinct members of `{P_ℓ, P'_ℓ : ℓ ≥ 1}` have a common nonzero root. -/
theorem commonRootsStatement (hI : FirstDerivativeIntegerInequalities)
    (hF : FirstDerivativeFactorDegreeChecks) (hDeng : DengLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros) :
    CommonRootsStatement :=
  commonRootsStatement_of_irreducible hH hZ
    (legendreAndDerivativesStatement hI hF hDeng hH hZ)

end ArithmeticOfJacobiPolynomials
