/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianArithmeticRealization

/-!
# Jacobian settings for the four families of the paper (§6.5)

`JacobianFamilyApplications` proves `FamilyArithmeticConclusions f` (Corollary 6.6 for *every*
  Jacobian
setting of `f`) for the four families of §6.5. This file is the realization
companion: for each family it proves that a `JacobianSetting f` exists, satisfying the
whole conclusion of Corollary 6.6 together with the realized witnesses of
`exists_jacobianSetting_arithmeticConclusions_realized`.

* `RealizedCitations` bundles the general, source-located citation `Prop`s needed to apply that
  theorem.
* `RealizedFamilyArithmeticConclusions f` is the entire existential conclusion of
  `exists_jacobianSetting_arithmeticConclusions_realized` for one polynomial `f`.
* The four families have exactly the ranges and polynomial hypotheses of
  `JacobianFamilyApplications`; the computer-verified `KanekoZagierFastCriterion` remains an
  explicit hypothesis of the Kaneko–Zagier family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace ArithmeticOfJacobiPolynomials

open AbelianBettiHodge ComplexRealization AbelianArithmetic EtaleCycleClassInterface
  FixedRationalParameters

/-- The general literature inputs needed to realize Corollary 6.6 on a Jacobian:
Milne's Jacobian existence, the `JacobianArithmeticCitations` bundle, and the cup-product,
  first-Chern, Betti
cycle class, Betti–Tate comparison and canonical cycle system existence statements of `External`. -/
structure RealizedCitations : Prop where
  /-- Existence of Jacobians (Milne, JV, Theorem 1.1 and Proposition 1.9). -/
  jacobianExists : Jacobian.JacobianExists.{0}
  /-- The citations of Corollary 6.6 itself. -/
  arithmeticCitations : JacobianArithmeticCitations
  /-- Cup products on the Betti cohomology of a torus. -/
  cupProduct : TorusBettiCupProduct
  /-- First Chern classes in Betti cohomology. -/
  firstChern : BettiFirstChernExists
  /-- Betti cycle class systems. -/
  bettiCycleClass : BettiCycleClassExists
  /-- Betti–Tate comparison. -/
  bettiTateComparison : BettiTateComparisonExists
  /-- Canonical cycle systems over number fields. -/
  canonicalCycleSystem : CanonicalCycleSystemExists

/-- The entire conclusion of `exists_jacobianSetting_arithmeticConclusions_realized` for one
  polynomial: an
Jacobian setting of `f` with the full conclusion of Corollary 6.6 (canonical cycle class
predicate), realized Hodge cycle data, Betti–Tate comparison data, Tate cycle systems, and an
origin-preserving base-change embedding `J_ℂ ⟶ J`. -/
def RealizedFamilyArithmeticConclusions (f : ℚ[X]) : Prop :=
  ∃ S : JacobianSetting f,
    S.ArithmeticConclusions CanonicalCycleClass ∧ S.HodgeCycleData ∧ S.BettiTateComparisonData ∧
    S.TateCycleData ∧
    ∃ emb : S.Jℂ.X.left ⟶ S.J.X.left,
      IsPullback emb S.Jℂ.X.hom S.J.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ∧ PreservesOrigin emb

/-- A realized family has a Jacobian setting. -/
theorem RealizedFamilyArithmeticConclusions.nonempty {f : ℚ[X]}
    (h : RealizedFamilyArithmeticConclusions f) :
    Nonempty (JacobianSetting f) :=
  let ⟨S, _⟩ := h
  ⟨S⟩

/-- **Realization for every `ZarhinHypotheses` polynomial**: the three hypotheses of Corollary 6.6
(§6.5) give a Jacobian setting with the realized conclusion. -/
theorem RealizedCitations.realized (R : RealizedCitations) {f : ℚ[X]} (hZ : ZarhinHypotheses f) :
    RealizedFamilyArithmeticConclusions f := by
  obtain ⟨hf, hd, hS⟩ := (zarhinHypotheses_iff f).mp hZ
  exact exists_jacobianSetting_arithmeticConclusions_realized
    R.jacobianExists R.arithmeticCitations R.cupProduct
    R.firstChern R.bettiCycleClass R.bettiTateComparison R.canonicalCycleSystem hf hd hS

/-- **The Kaneko–Zagier families** (§6.5): for `λ, μ ∈ {±1}` and every `d ≥ 9`, an
Jacobian setting of `P_d^{(λ/3, μ/2)}` realizes Corollary 6.6. Takes the computer-verified
`KanekoZagierFastCriterion` (Appendix B.2) and the cited results of Theorem 1.1, exactly as
`JacobianArithmeticCitations.arithmeticConclusions_kanekoZagierJacobi`. -/
theorem RealizedCitations.realized_kanekoZagierJacobi (R : RealizedCitations)
    (hC : KanekoZagierFastCriterion) (hCHK : CullinanHajirKanekoZagierIrreducibility)
    (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) (hH : HansonLcmBound) (hT : BMORThetaBound)
    (hS : BMORThetaSmallBound) (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHKG : CullinanHajirKanekoZagierGalois) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {d : ℕ} (hd : 9 ≤ d) :
    RealizedFamilyArithmeticConclusions (kanekoZagierJacobi l μ d) :=
  R.realized
    (zarhinHypotheses_kanekoZagierJacobi' hC hCHK hZ hNP hH hT hS hBMOR hBT hJones hCHKG hl hμ hd)

/-- **Unequal integer parameters** (§6.5): for distinct `a, b ∈ ℕ` there is `N` such that for
every `d ≥ max 9 N` a Jacobian setting of `P_d^{(a,b)}` realizes Corollary 6.6
(Theorem 1.3). -/
theorem RealizedCitations.exists_realized_jacobiP (R : RealizedCitations) (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
    (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, ∀ d ≥ max 9 N, RealizedFamilyArithmeticConclusions (jacobiP a b d) := by
  obtain ⟨N, hN⟩ := exists_zarhinHypotheses_jacobiP hH hZ hJordan hEis hdisc hDusart hab
  exact ⟨N, fun d hd => R.realized (hN d hd)⟩

/-- **Dominant factors of Theorem 1.6** (§6.5): under the denominator condition there is
`N` such that for every `n ≥ N` every dominant factor `h` of `P_n^{(α,β)}` has degree at
least nine and a Jacobian setting of `h` realizes Corollary 6.6. -/
theorem RealizedCitations.exists_realized_dominant_jacobiP (R : RealizedCitations)
    (hBMOR : BMORPrimeCountingBound) (h619 : BMORLargeModulusPrimeCounting)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem) {α β : ℚ}
    (hcond : DenomCond α β) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ h : ℚ[X], IsDominant (jacobiP α β n) h →
      9 ≤ h.natDegree ∧ RealizedFamilyArithmeticConclusions h := by
  obtain ⟨N, hN⟩ := exists_zarhinHypotheses_dominant_jacobiP hBMOR h619 hBT hJones hcond
  refine ⟨N, fun n hn h hh => ?_⟩
  exact ⟨((zarhinHypotheses_iff h).mp (hN n hn h hh)).2.1, R.realized (hN n hn h hh)⟩

/-- **Derivative families** (§6.5): for fixed `r` there is `N` such that for every
`m ≥ max 9 N` and `δ ≤ 1` a Jacobian setting of `Q_{m,r,δ}` realizes Corollary 6.6
(Corollary 1.7 with `E = ℚ`). -/
theorem RealizedCitations.exists_realized_reducedGegenbauerSquare (R : RealizedCitations)
    (hQ : GegenbauerQuadraticTransformation) (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    (hBMOR : BMORPrimeCountingBound) (h619 : BMORLargeModulusPrimeCounting)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem) (r : ℕ) :
    ∃ N : ℕ, ∀ m ≥ max 9 N, ∀ δ : ℕ, δ ≤ 1 →
      RealizedFamilyArithmeticConclusions (reducedGegenbauerSquare m r δ) := by
  obtain ⟨N, hN⟩ :=
    exists_zarhinHypotheses_reducedGegenbauerSquare hQ hH hZ hBMOR h619 hBT hJones r
  exact ⟨N, fun m hm δ hδ => R.realized (hN m hm δ hδ)⟩

end ArithmeticOfJacobiPolynomials

end
