/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.JacobianFamilyApplications
public import ArithmeticOfJacobiPolynomials.Applications.JacobianTateCycleData
public import ArithmeticOfJacobiPolynomials.Applications.JacobianArithmeticWitnesses
public import ArithmeticOfJacobiPolynomials.Applications.JacobianSettingExistence

/-!
# Corollary 6.6 with its realized witnesses

The theorem `exists_jacobianSetting_arithmeticConclusions_realized` bundles, for one
Jacobian setting `S` of `y² = f(x)`, the complete conclusion of Corollary 6.6 with the realized
objects its statements quantify over:

* `S.ArithmeticConclusions CanonicalCycleClass`, the entire conclusion;
* `S.HodgeCycleData`: uniformizations, cup comparisons, first-Chern maps and Betti cycle class
  systems on every positive power of `J_ℂ`, in every codimension;
* `S.BettiTateComparisonData`: a Tate basis witnessing the Betti–Tate comparison for every
  complex base change, uniformization and rational basis;
* `S.TateCycleData`: canonical cycle systems on every number-field base change of every positive
  power of `J`;
* an origin-preserving pullback `emb : J_ℂ ⟶ J` over `Spec ℚ → Spec ℂ`.

The inputs are only the general literature results (`Jacobian.JacobianExists`,
  `JacobianArithmeticCitations`,
the cup-product, first-Chern, Betti cycle class, Betti–Tate comparison and canonical cycle
system existence statements of `External.lean`) and the hypotheses on `f`.
`exists_bettiTateWitness` exhibits, for any prime `ℓ`, one concrete
instance `(σ, emb, U, n, bV, bW)` of the comparison condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace ArithmeticOfJacobiPolynomials

open AbelianBettiHodge ComplexRealization AbelianArithmetic EtaleCycleClassInterface

namespace JacobianSetting

variable {f : ℚ[X]} (S : JacobianSetting f)

/-- **One Betti–Tate comparison instance** on the setting `S`, for every prime `ℓ`:
an embedding `σ : ℚ̄ → ℂ` (Mathlib's `IsAlgClosed.lift`), the origin-preserving base-change
pullback `emb`, a uniformization `U` of `J_ℂ`, the finite dimension `n` of
`H₁(J_ℂ(ℂ), ℚ)` with `bV = Module.finBasis`, and the Tate basis `bW` from the general
comparison existence statement, satisfying `IsBettiTateComparison`. -/
theorem exists_bettiTateWitness (hUnif : ComplexUniformization)
    (hComp : BettiTateComparisonExists) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (σ : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) (emb : S.Jℂ.X.left ⟶ S.J.X.left)
      (_ : IsPullback emb S.Jℂ.X.hom S.J.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
      (_ : PreservesOrigin emb) (U : UniformizationData S.Jℂ.X) (n : ℕ)
      (bV : Module.Basis (Fin n) ℚ (bettiOne S.Jℂ.X))
      (bW : Module.Basis (Fin n) ℚ_[ℓ]
        (rationalTate ℓ (GroupScheme.GeomPoints ℚ (AlgebraicClosure ℚ) S.J.X))),
      IsBettiTateComparison U emb σ ℓ bV bW := by
  have := S.isJacobianℂ.isAbelianVariety
  obtain ⟨emb, hemb, h0⟩ := S.exists_baseChange_embedding
  obtain ⟨U⟩ := hUnif S.Jℂ.X
  have := U.finiteDimensional_bettiOne S.Jℂ.X
  let σ : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let bV := Module.finBasis ℚ (bettiOne S.Jℂ.X)
  obtain ⟨bW, hbW⟩ := S.bettiTateComparisonData hComp σ emb hemb h0 U ℓ bV
  exact ⟨σ, emb, hemb, h0, U, _, bV, bW, hbW⟩

end JacobianSetting

/-- **Corollary 6.6 with realized witnesses**. For `f` separable of degree `≥ 9`
with symmetric Galois group, and only the general literature inputs, there is a Jacobian
setting `S` satisfying the complete conclusion of Corollary 6.6 (for the canonical cycle class
predicate), together with realized Hodge cycle data, Betti–Tate comparison data, Tate cycle systems
and an origin-preserving base-change embedding `J_ℂ ⟶ J`. -/
theorem exists_jacobianSetting_arithmeticConclusions_realized
    (hJ : Jacobian.JacobianExists.{0}) (C : JacobianArithmeticCitations)
    (hCup : TorusBettiCupProduct) (hChern : BettiFirstChernExists)
    (hBC : BettiCycleClassExists) (hComp : BettiTateComparisonExists)
    (hEtale : CanonicalCycleSystemExists)
    {f : ℚ[X]} (hf : f.Separable) (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) :
    ∃ S : JacobianSetting f,
      S.ArithmeticConclusions CanonicalCycleClass ∧ S.HodgeCycleData ∧ S.BettiTateComparisonData ∧
      S.TateCycleData ∧
      ∃ emb : S.Jℂ.X.left ⟶ S.J.X.left,
        IsPullback emb S.Jℂ.X.hom S.J.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ∧ PreservesOrigin emb := by
  have hZ : ZarhinHypotheses f := (zarhinHypotheses_iff f).mpr ⟨hf, hd, hS⟩
  have hd0 : 0 < f.natDegree := by omega
  obtain ⟨S⟩ := exists_jacobianSetting hJ hf hd0
  exact ⟨S, C.familyArithmeticConclusions hZ S, S.hodgeCycleData C.uniformization hCup hChern hBC,
    S.bettiTateComparisonData hComp, S.tateCycleData hEtale hf hd0,
    S.exists_baseChange_embedding⟩

end ArithmeticOfJacobiPolynomials

end
