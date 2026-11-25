/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteRange
public import ArithmeticOfJacobiPolynomials.Applications.ZarhinHypotheses

/-!
# Theorem 1.1 (the Mahlburg–Ono conjecture)

`mahlburgOnoStatement` proves `MahlburgOnoStatement` from the cited literature and the computed
input `KanekoZagierFastCriterion` (`ComputerVerified`, see `External.lean`): the range
`1 ≤ n ≤ 8332` is the computation of Cullinan–Hajir [CHK, Remark 4.6]; Proposition B.2
(`kanekoZagierFiniteRange_holds`, the hand reduction of the manuscript applied to the computed
comparisons) covers `8333 ≤ n ≤ 250000`; Proposition B.1 (`kanekoZagier_explicit_cutoff`) covers
`n ≥ 250000`; the Galois group is `S_n` by Theorem 5.12.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Theorem 1.1 (the Mahlburg–Ono conjecture).** For `λ, μ ∈ {±1}` and every `n ≥ 1`,
`P_n^{(λ/3, μ/2)}` is irreducible over `ℚ` with Galois group `S_n`. Conditional only on the
computed input `hC` and the cited results named in the hypotheses. -/
theorem mahlburgOnoStatement (hC : KanekoZagierFastCriterion)
    (hCHK : CullinanHajirKanekoZagierIrreducibility)
    (hZ : JacobiSimpleRealZeros) (hNP : NewtonPolygonRootSlopes) (hH : HansonLcmBound)
    (hT : BMORThetaBound) (hS : BMORThetaSmallBound) (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHKG : CullinanHajirKanekoZagierGalois) : MahlburgOnoStatement :=
  mahlburgOno_of_finiteRange hCHK (kanekoZagierFiniteRange_holds hC hZ hNP) hZ hNP hH hT hS hBMOR
    hBT hJones hCHKG

/-- The Kaneko–Zagier family satisfies the hypotheses of Corollary 6.6 in every degree `d ≥ 9`,
conditional only on the computed input `hC` and cited results. -/
theorem zarhinHypotheses_kanekoZagierJacobi' (hC : KanekoZagierFastCriterion)
    (hCHK : CullinanHajirKanekoZagierIrreducibility)
    (hZ : JacobiSimpleRealZeros) (hNP : NewtonPolygonRootSlopes) (hH : HansonLcmBound)
    (hT : BMORThetaBound) (hS : BMORThetaSmallBound) (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHKG : CullinanHajirKanekoZagierGalois) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {d : ℕ} (hd : 9 ≤ d) :
    ZarhinHypotheses (kanekoZagierJacobi l μ d) :=
  zarhinHypotheses_kanekoZagierJacobi hCHK (kanekoZagierFiniteRange_holds hC hZ hNP) hZ hNP hH hT hS
    hBMOR hBT hJones hCHKG hl hμ hd

end ArithmeticOfJacobiPolynomials
