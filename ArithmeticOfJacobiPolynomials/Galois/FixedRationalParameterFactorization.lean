/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParametersFixedField
public import ArithmeticOfJacobiPolynomials.MainResults

/-!
# Theorem 1.6 (fixed rational parameters)

`ArithmeticOfJacobiPolynomials.fixedRationalParametersStatement` proves
`FixedRationalParametersStatement` from
`fixedRationalParameters_unfolded` (whose `IsDominant`, `DenomCond` are `IsDominantFactor` and
`JacobiDenominatorCondition` verbatim). Conditional on [BMOR, Corollary 1.7],
[BMOR, Proposition 6.19], [MV, Theorem 2] and [Jones, Corollary 1.3].
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Theorem 1.6.** -/
theorem fixedRationalParametersStatement (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) : FixedRationalParametersStatement :=
  FixedRationalParameters.fixedRationalParameters_unfolded hBMOR h619 hBT hJones

end ArithmeticOfJacobiPolynomials
