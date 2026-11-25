/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianArithmeticConsequences
public import ArithmeticOfJacobiPolynomials.Applications.ZarhinHypotheses
public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParametersDerivatives
public import ArithmeticOfJacobiPolynomials.KanekoZagier.IrreducibilityAndGalois

/-!
# Corollary 6.6 for the polynomial families of the paper (§6.5)

Manuscript §6.5 applies Corollary 6.6 to four families by checking its hypotheses
(`f` separable of degree `≥ 9` with Galois group `S_{deg f}`, `ZarhinHypotheses`):

1. the four Kaneko–Zagier families `P_d^{(λ/3, μ/2)}`, `λ, μ ∈ {±1}`, `d ≥ 9`
   (`arithmeticConclusions_kanekoZagierJacobi`, from Theorem 1.1);
2. `P_d^{(a,b)}` for fixed unequal `a, b ∈ ℕ` and `d ≥ max {9, N(a,b)}`
   (`exists_arithmeticConclusions_jacobiP`, from Theorem 1.3);
3. every dominant factor of `P_n^{(α,β)}` in Theorem 1.6, with its degree `≥ 9`, for all
   `n ≥ N` (`exists_arithmeticConclusions_dominant_jacobiP`);
4. the derivative families `Q_{m,r,δ}` for fixed `r`, `m ≥ max {9, N}` and `δ ∈ {0, 1}`
   (`exists_arithmeticConclusions_reducedGegenbauerSquare`, from Corollary 1.7).

The `ZarhinHypotheses` theorems verify the arithmetic hypotheses.
`JacobianArithmeticCitations` bundles the general literature inputs, including Zarhin
Theorem 8.1. The cycle-class conclusion is derived by finite-stage representation
and rational averaging in `JacobianSetting.arithmeticConclusions`; every family below takes
only the general citations and its proved polynomial hypotheses.
-/

@[expose] public section

open Polynomial

namespace ArithmeticOfJacobiPolynomials

open FixedRationalParameters

/-- The general, source-numbered cited inputs of Corollary 6.6 (Zarhin and Milne/Mumford, stated
in their full generality in `External`). -/
structure JacobianArithmeticCitations : Prop where
  /-- Zarhin Theorem 2.4. -/
  endomorphisms : Zarhin.GeometricEndomorphisms.{0}
  /-- Existence of the canonical principal polarization of a Jacobian. -/
  canonicalPolarization : Jacobian.CanonicalPrincipalPolarizationExists.{0}
  /-- Complex uniformization of complex abelian varieties. -/
  uniformization : AbelianBettiHodge.ComplexUniformization
  /-- Riemann form of a polarization (Milne, *Abelian varieties*, I Ex. 13.3). -/
  riemannForm : AbelianBettiHodge.PolarizationRiemannForm
  /-- Zarhin Theorem 9.1 proof / Remark 9.2: Hodge and Mumford–Tate groups. -/
  hodgeMumfordTate : Zarhin.HodgeAndMumfordTateGroups
  /-- Existence of Weil pairings. -/
  weilPairingsExist : AbelianVariety.WeilPairingsExist.{0}
  /-- Weil pairings of a polarization are alternating. -/
  weilAlternating : AbelianVariety.PolarizedWeilAlternating.{0}
  /-- Zarhin Theorem 2.6. -/
  tateLie : Zarhin.TateLieAlgebra.{0}
  /-- Zarhin Theorem 9.1: Hodge classes are combinations of divisor products. -/
  hodgeClassDivisorProducts : JacobianArithmeticInputs.HodgeClassDivisorProducts
  /-- Zarhin Theorem 8.1, characteristic-zero assertion. -/
  tateClassDivisorProducts : Zarhin.TateClassesDivisorProducts
  /-- Zarhin Remark 9.2 over `ℚ`. -/
  mumfordTateLie : JacobianArithmeticInputs.MumfordTateLieEquality

/-- Corollary 6.6 for every realized Jacobian setting of the polynomial,
with its canonical cycle-class predicate. -/
def FamilyArithmeticConclusions (f : ℚ[X]) : Prop :=
  ∀ S : JacobianSetting f,
    S.ArithmeticConclusions EtaleCycleClassInterface.CanonicalCycleClass

/-- **Corollary 6.6 for every `f` satisfying `ZarhinHypotheses`** (§6.5): the three
hypotheses of the corollary are exactly the hypotheses of `ZarhinHypotheses`. -/
theorem JacobianArithmeticCitations.familyArithmeticConclusions
    (C : JacobianArithmeticCitations) {f : ℚ[X]} (hZ : ZarhinHypotheses f) :
    FamilyArithmeticConclusions f := by
  intro S
  obtain ⟨hf, hd, hS⟩ := (zarhinHypotheses_iff f).mp hZ
  exact S.arithmeticConclusions C.tateClassDivisorProducts C.endomorphisms C.canonicalPolarization
    C.uniformization C.riemannForm C.hodgeMumfordTate C.weilPairingsExist C.weilAlternating
    C.tateLie C.hodgeClassDivisorProducts C.mumfordTateLie hf hd hS

/-- **The Kaneko–Zagier families** (§6.5). For `λ, μ ∈ {±1}` and every `d ≥ 9`,
Corollary 6.6 applies to `f = P_d^{(λ/3, μ/2)}`. Takes the computer-verified input
`KanekoZagierFastCriterion` (Appendix B.2) and the cited results of Theorem 1.1. -/
theorem JacobianArithmeticCitations.arithmeticConclusions_kanekoZagierJacobi
    (C : JacobianArithmeticCitations)
    (hC : KanekoZagierFastCriterion) (hCHK : CullinanHajirKanekoZagierIrreducibility)
    (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) (hH : HansonLcmBound) (hT : BMORThetaBound)
    (hS : BMORThetaSmallBound) (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHKG : CullinanHajirKanekoZagierGalois) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {d : ℕ} (hd : 9 ≤ d) :
    FamilyArithmeticConclusions (kanekoZagierJacobi l μ d) :=
  C.familyArithmeticConclusions
    (zarhinHypotheses_kanekoZagierJacobi' hC hCHK hZ hNP hH hT hS hBMOR hBT hJones hCHKG hl hμ hd)

/-- **Unequal integer parameters** (§6.5). For distinct `a, b ∈ ℕ` there is an explicit
threshold `N(a,b)` such that Corollary 6.6 applies to `P_d^{(a,b)}` for every `d ≥ max {9, N}`
(Theorem 1.3). -/
theorem JacobianArithmeticCitations.exists_arithmeticConclusions_jacobiP
    (C : JacobianArithmeticCitations) (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
    (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, ∀ d ≥ max 9 N, FamilyArithmeticConclusions (jacobiP a b d) := by
  obtain ⟨N, hN⟩ := exists_zarhinHypotheses_jacobiP hH hZ hJordan hEis hdisc hDusart hab
  exact ⟨N, fun d hd => C.familyArithmeticConclusions (hN d hd)⟩

/-- **Dominant factors of Theorem 1.6** (§6.5). Under the denominator condition, there is
a threshold `N` such that for every `n ≥ N` every dominant factor `h` of `P_n^{(α,β)}` has
degree at least nine and Corollary 6.6 applies to `h`. -/
theorem JacobianArithmeticCitations.exists_arithmeticConclusions_dominant_jacobiP
    (C : JacobianArithmeticCitations)
    (hBMOR : BMORPrimeCountingBound) (h619 : BMORLargeModulusPrimeCounting)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem) {α β : ℚ}
    (hcond : DenomCond α β) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ h : ℚ[X], IsDominant (jacobiP α β n) h →
      9 ≤ h.natDegree ∧ FamilyArithmeticConclusions h := by
  obtain ⟨N, hN⟩ := exists_zarhinHypotheses_dominant_jacobiP hBMOR h619 hBT hJones hcond
  refine ⟨N, fun n hn h hh => ?_⟩
  exact ⟨((zarhinHypotheses_iff h).mp (hN n hn h hh)).2.1,
    C.familyArithmeticConclusions (hN n hn h hh)⟩

/-- **Derivative families** (§6.5). For fixed `r` there is a threshold `N` such that
Corollary 6.6 applies to `Q_{m,r,δ}` for every `m ≥ max {9, N}` and `δ ∈ {0, 1}`
(Corollary 1.7 with `E = ℚ`). -/
theorem JacobianArithmeticCitations.exists_arithmeticConclusions_reducedGegenbauerSquare
    (C : JacobianArithmeticCitations)
    (hQ : GegenbauerQuadraticTransformation) (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    (hBMOR : BMORPrimeCountingBound) (h619 : BMORLargeModulusPrimeCounting)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem) (r : ℕ) :
    ∃ N : ℕ, ∀ m ≥ max 9 N, ∀ δ : ℕ, δ ≤ 1 →
      FamilyArithmeticConclusions (reducedGegenbauerSquare m r δ) := by
  obtain ⟨N, hN⟩ :=
    exists_zarhinHypotheses_reducedGegenbauerSquare hQ hH hZ hBMOR h619 hBT hJones r
  exact ⟨N, fun m hm δ hδ => C.familyArithmeticConclusions (hN m hm δ hδ)⟩

end ArithmeticOfJacobiPolynomials
