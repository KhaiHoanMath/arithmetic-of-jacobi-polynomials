/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.IntegralParameters
public import ArithmeticOfJacobiPolynomials.Galois.UnequalParametersGalois

/-!
# Corollary 6.1 (all integral parameters with unequal absolute values)

`ArithmeticOfJacobiPolynomials.integralParametersStatement` proves `IntegralParametersStatement`,
combining the
reduction `integralParametersStatement_of_galois` with Theorem 1.3's Galois part
(`exists_forall_galoisGroupIsSymmetric_jacobiP`). Conditional on `HansonLcmBound`,
`JacobiSimpleRealZeros`, `JordanPrimeCycleTheorem`, `EisensteinPrimeTotallyRamified`,
`JacobiDiscriminantFormula` and `DusartThetaBound`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Corollary 6.1.** For integers `a, b` with `|a| ≠ |b|`, for all sufficiently large `n`,
`P_n^{(a,b)}(x)/((x-1)^{a_-}(x+1)^{b_-})` is irreducible over `ℚ` with Galois group
`S_{n - a_- - b_-}`. -/
theorem integralParametersStatement (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
    (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula)
    (hDusart : DusartThetaBound) : IntegralParametersStatement :=
  integralParametersStatement_of_galois hH hZ fun _ _ hab =>
    exists_forall_galoisGroupIsSymmetric_jacobiP hH hZ hJordan hEis hdisc hDusart hab

end ArithmeticOfJacobiPolynomials
