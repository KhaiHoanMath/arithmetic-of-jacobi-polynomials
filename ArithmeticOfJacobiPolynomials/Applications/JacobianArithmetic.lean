/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianArithmeticInterface
public import ArithmeticOfJacobiPolynomials.Applications.JacobianDimension
public import ArithmeticOfJacobiPolynomials.Applications.JacobianEndomorphisms
public import ArithmeticOfJacobiPolynomials.Applications.JacobianHodgeGroups
public import ArithmeticOfJacobiPolynomials.Applications.JacobianPolarization
public import ArithmeticOfJacobiPolynomials.Applications.JacobianWeilPairing
public import ArithmeticOfJacobiPolynomials.Applications.JacobianZarhinLie
public import ArithmeticOfJacobiPolynomials.Algebra.AbelianTateLie
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianVarietyProduct
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiGroups
public import ArithmeticOfJacobiPolynomials.Applications.AbelianTorusCohomology

/-!
# Corollary 6.6: Jacobians of hyperelliptic curves with symmetric Galois group

Manuscript Corollary 6.6. Let `f ∈ ℚ[x]` be separable of degree `d ≥ 9` with
`Gal(f/ℚ) = S_d` and `J_f` the Jacobian of the smooth projective curve `y² = f(x)`. Then

1. `dim J_f = ⌊(d-1)/2⌋` (`JacobianSetting.Dimension`) and `End_{ℚ̄}(J_f) = ℤ`
   (`JacobianSetting.EndomorphismRing`);
2. for `V = H₁(J_f(ℂ), ℚ)` and `ψ` the Riemann form of the canonical principal polarization,
   `Hdg(J_f) = Sp(V, ψ)` and `MT(J_f) = GSp(V, ψ)` (`HodgeGroups`);
3. for every number field `K ⊂ ℚ̄`, prime `ℓ` and power `J_f^r`, the image of `Gal(ℚ̄/K)` on
   `V_ℓ` has Lie algebra `ℚ_ℓ Id ⊕ 𝔰𝔭(V_ℓ, ψ_ℓ)` for the alternating Weil pairing `ψ_ℓ` of the
   canonical principal polarization, and its image on `V_ℓ(J^r)` is the diagonal (`TateLie`);
4. every rational Hodge class on every power `J_f^h` is a `ℚ`-linear combination of products of
   divisor classes (`HodgeClasses`);
5. for every `h ≥ 1`, `c ≥ 0` and number field `K`, the cycle class map
   `CH^c((J_f^h)_K) ⊗ ℚ_ℓ → H^{2c}_ét((J_f^h)_{ℚ̄}, ℚ_ℓ(c))^{Gal(ℚ̄/K)}` is surjective
   (`CycleClasses`).

The conjunction is `JacobianSetting.ArithmeticConclusions`. The model is
`Hyperelliptic.projectiveModel f`, the Jacobians represent the relative Picard sheaf
(`Jacobian.IsJacobianOf`), `V` is singular homology of the analytic space, `V_ℓ` is the
rational Tate module of Stacks' group of geometric points, and cohomology is `ℓ`-adic cohomology of
Stacks. The interfaces are characterized by
`Jacobian.IsCanonicalPrincipalPolarization`, `AbelianBettiHodge.PolarizationForm`,
`AbelianArithmetic.IsBettiFirstChern` and `AbelianArithmetic.CycleClassPredicate`.

## What is proved and what is cited

* `JacobianSetting.Dimension`: Stacks genus plus the proved hyperelliptic genus formula;
* `EndomorphismRing`: Zarhin Theorem 2.4 (`Zarhin.GeometricEndomorphisms`);
* `HodgeGroups`: Zarhin Theorem 9.1 proof / Remark 9.2 (`Zarhin.HodgeAndMumfordTateGroups`);
* `TateLie`: Zarhin Theorem 2.6 (`Zarhin.TateLieAlgebra`) plus the manuscript's finite-index and
  diagonal-power transfers (proved in `JacobianTateLie`);
* `HodgeClasses`: Zarhin Theorem 9.1 (`JacobianArithmeticInputs.HodgeClassDivisorProducts`, in
  `External.lean`);
* `CycleClasses`: Zarhin Theorem 8.1 plus the manuscript's own averaging descent
  (`AbelianCycleClass.span_range_clBase_eq_invariants`); it is relative to the canonical cycle class
  predicate `Canon` of the curves interface (`AbelianCycleClass`), which is not defined here;
* `MumfordTateConjecture`: Zarhin Remark 9.2 over `ℚ`, transferred to number fields by the
  finite-index argument; the comparison is the characterized `IsBettiTateComparison`.

The concluding sentence (Corollary 6.6), *the Hodge, Tate and Mumford–Tate conjectures hold for
`J_f` and all its powers*, is stated in full: `HodgeConjecture` (Hodge classes lie in the `ℚ`-span
of the classes of algebraic cycles, relative to any characterized `BettiCycleClassSystem`),
`CycleClasses` (which *is* the Tate conjecture for every `J_f^h` over every number field) and
`MumfordTateConjecture` (relative to the characterized comparison `IsBettiTateComparison`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace ArithmeticOfJacobiPolynomials

open ArithmeticOfJacobiPolynomials.GroupObject GroupScheme AbelianTateLie

open AbelianBettiHodge AbelianBettiCohomology AbelianHodgeClasses AbelianArithmetic
  AbelianEtale AbelianCycleClass ComplexRealization

/-! ### The setting: one Jacobian, its geometric base changes, and a big fppf site -/

/-- The data in which the conjuncts of Corollary 6.6 are stated: a big fppf site containing the
smooth projective hyperelliptic model of `y² = f(x)` over `ℚ`, `ℚ̄` and `ℂ` and their base schemes,
and Jacobians (`Jacobian.IsJacobianOf`) of the three models. Every field of the structure is a
hypothesis that holds for any Jacobian; the Jacobians over `ℚ̄` and `ℂ` are Jacobians of the
base-changed curve and are therefore the base changes of `J`
(`Jacobian.BaseChange.isJacobianOf_baseChange`,
`Jacobian.IsJacobianOf.exists_grpIso`). -/
structure JacobianSetting (f : ℚ[X]) where
  /-- The big fppf site. -/
  B : BigFppfSite.{0}
  hC : B.Contains (Hyperelliptic.projectiveModel f)
  hQ : B.Contains (Spec (.of ℚ))
  g : B.obj hC ⟶ B.obj hQ
  hg : B.inclusion.map g = Hyperelliptic.toSpecField f
  proper : IsProper (B.inclusion.map g)
  hdim : topologicalKrullDim (Hyperelliptic.projectiveModel f) ≤ 1
  /-- The Jacobian `J_f` over `ℚ`. -/
  J : Grp (Over (Spec (.of ℚ)))
  isJacobian : Jacobian.IsJacobianOf B hC hQ g hdim J
  comm : IsCommMonObj J.X
  hL : B.Contains (Spec (.of (AlgebraicClosure ℚ)))
  hCL : B.Contains (Hyperelliptic.projectiveModel (f.map (algebraMap ℚ (AlgebraicClosure ℚ))))
  gL : B.obj hCL ⟶ B.obj hL
  hgL : B.inclusion.map gL =
    Hyperelliptic.toSpecField (f.map (algebraMap ℚ (AlgebraicClosure ℚ)))
  properL : IsProper (B.inclusion.map gL)
  hdimL : topologicalKrullDim
    (Hyperelliptic.projectiveModel (f.map (algebraMap ℚ (AlgebraicClosure ℚ)))) ≤ 1
  /-- The Jacobian over `ℚ̄`. -/
  JL : Grp (Over (Spec (.of (AlgebraicClosure ℚ))))
  isJacobianL : Jacobian.IsJacobianOf B hCL hL gL hdimL JL
  hℂ : B.Contains (Spec (.of ℂ))
  hCℂ : B.Contains (Hyperelliptic.projectiveModel (f.map (algebraMap ℚ ℂ)))
  gℂ : B.obj hCℂ ⟶ B.obj hℂ
  hgℂ : B.inclusion.map gℂ = Hyperelliptic.toSpecField (f.map (algebraMap ℚ ℂ))
  properℂ : IsProper (B.inclusion.map gℂ)
  hdimℂ : topologicalKrullDim (Hyperelliptic.projectiveModel (f.map (algebraMap ℚ ℂ))) ≤ 1
  /-- The Jacobian over `ℂ`. -/
  Jℂ : Grp (Over (Spec (.of ℂ)))
  isJacobianℂ : Jacobian.IsJacobianOf B hCℂ hℂ gℂ hdimℂ Jℂ

attribute [instance] JacobianSetting.proper JacobianSetting.properL JacobianSetting.properℂ
  JacobianSetting.comm

namespace JacobianSetting

open AbelianBettiHodge AbelianBettiCohomology AbelianHodgeClasses AbelianArithmetic
  AbelianEtale AbelianCycleClass ComplexRealization

variable {f : ℚ[X]} (S : JacobianSetting f)

/-- **`dim J_f = ⌊(d - 1)/2⌋`** (Corollary 6.6). -/
def Dimension : Prop :=
  Stacks.Groupoids.abelianVarietyDimension S.J.X = (f.natDegree - 1) / 2

/-- **`End_{ℚ̄}(J_f) = ℤ`** (Corollary 6.6): the endomorphism ring of the Jacobian of the
base-changed curve over `ℚ̄` is `ℤ`. -/
def EndomorphismRing : Prop :=
  letI := S.isJacobianL.isAbelianVariety
  letI := isCommMonObj_of_isProper_of_geometricallyIntegral S.JL.X
  Nonempty (GrpObjEnd S.JL.X ≃+* ℤ)

/-- **The canonical principal polarization and its Riemann form exist** on the complex Jacobian:
a canonical principal polarization, uniformization data and the characterized Riemann form on the
`H₁(J(ℂ), ℚ)` (Corollary 6.6). -/
def HodgeGroupData : Prop :=
  ∃ (D : Grp (Over (Spec (.of ℂ)))) (P : Stacks.Picard.ofScheme (S.Jℂ.X ⊗ D.X).left)
    (φ : S.Jℂ.X ⟶ D.X) (_ : IsMonHom φ),
    Jacobian.IsCanonicalPrincipalPolarization
      (Over.mk (Hyperelliptic.toSpecField (f.map (algebraMap ℚ ℂ)))) S.Jℂ D.X P φ ∧
    ∃ (U : UniformizationData S.Jℂ.X), Nonempty (PolarizationForm S.Jℂ.X U D.X P φ)

/-- **`Hdg(J_f) = Sp(V, ψ)` and `MT(J_f) = GSp(V, ψ)`** for `V = H₁(J_f(ℂ), ℚ)` and `ψ` the Riemann
form of the canonical principal polarization (Corollary 6.6). -/
def HodgeGroups : Prop :=
  ∀ (D : Over (Spec (.of ℂ))) [GrpObj D] (P : Stacks.Picard.ofScheme (S.Jℂ.X ⊗ D).left)
    (φ : S.Jℂ.X ⟶ D) [IsMonHom φ]
    (_ : Jacobian.IsCanonicalPrincipalPolarization
      (Over.mk (Hyperelliptic.toSpecField (f.map (algebraMap ℚ ℂ)))) S.Jℂ D P φ)
    (U : UniformizationData S.Jℂ.X) (F : PolarizationForm S.Jℂ.X U D P φ),
    U.canonicalHodge.hodgeGroup = symplecticGroup F.riemann.form ∧
      U.canonicalHodge.mumfordTateGroup = similitudeGroup F.riemann.form

/-- **The `ℓ`-adic Lie algebra** (Corollary 6.6), on the rational Tate module
`V_ℓ = T_ℓ(J_f(ℚ̄)) ⊗ ℚ_ℓ`. (1) A canonical principal polarization exists. (2) It has an alternating
perfect Weil pairing `ψ_ℓ` on `V_ℓ`. (3) For every geometric Weil pairing `ψ_ℓ` of it, every number
field `K ⊂ ℚ̄` and every power `r ≥ 1`: the Galois image lies in `GSp(V_ℓ, ψ_ℓ)`, the Galois image
of `Gal(ℚ̄/K)` on `V_ℓ` has Lie algebra `ℚ_ℓ Id ⊕ 𝔰𝔭(V_ℓ, ψ_ℓ)`, and on `V_ℓ(J^r)` it acts
diagonally with the diagonal Lie algebra. -/
def TateLie : Prop :=
  (∃ (D : Grp (Over (Spec (.of ℚ)))) (P : Stacks.Picard.ofScheme (S.J.X ⊗ D.X).left)
    (φ : S.J.X ⟶ D.X) (_ : IsMonHom φ),
      Jacobian.IsCanonicalPrincipalPolarization (Over.mk (Hyperelliptic.toSpecField f))
        S.J D.X P φ) ∧
  (∀ (D : Over (Spec (.of ℚ))) [GrpObj D] [IsCommMonObj D]
    (P : Stacks.Picard.ofScheme (S.J.X ⊗ D).left) (φ : S.J.X ⟶ D) [IsMonHom φ]
    (_ : Jacobian.IsCanonicalPrincipalPolarization (Over.mk (Hyperelliptic.toSpecField f))
      S.J D P φ) (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ W : DualPairingData ℓ (AlgebraicClosure ℚ) S.J.X D,
      WeilPairingGeometry.IsWeilData (AlgebraicClosure ℚ) S.J.X D W P ∧
        LinearMap.IsAlt (abelianWeilPairing W φ) ∧ Function.Bijective (abelianWeilPairing W φ)) ∧
  (∀ (D : Over (Spec (.of ℚ))) [GrpObj D] [IsCommMonObj D]
    (P : Stacks.Picard.ofScheme (S.J.X ⊗ D).left) (φ : S.J.X ⟶ D) [IsMonHom φ]
    (_ : Jacobian.IsCanonicalPrincipalPolarization (Over.mk (Hyperelliptic.toSpecField f))
      S.J D P φ) (ℓ : ℕ) [Fact ℓ.Prime] (W : DualPairingData ℓ (AlgebraicClosure ℚ) S.J.X D)
    (_ : WeilPairingGeometry.IsWeilData (AlgebraicClosure ℚ) S.J.X D W P) (m : ℕ)
    (b : Module.Basis (Fin m) ℚ_[ℓ] (rationalTate ℓ (GeomPoints ℚ (AlgebraicClosure ℚ) S.J.X)))
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] (r : ℕ) [NeZero r],
    (tateGaloisUnits S.J.X b).range ≤
        similitudeUnits (transportForm b.equivFun (abelianWeilPairing W φ)) ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (tateGaloisUnits S.J.X b)) =
        scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing W φ)) ∧
      ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits b r)) =
        AbelianTateLie.diagHom (ℓ := ℓ) (W := Fin m → ℚ_[ℓ]) r ''
          scalarPlusSymplectic ℓ (transportForm b.equivFun (abelianWeilPairing W φ)))

/-- **Rational Hodge classes on every power of `J_f`** are `ℚ`-linear combinations of products of
divisor classes (Corollary 6.6): in `H^{2c}(J_f^h(ℂ), ℚ) ≃ ⋀^{2c} H¹` (cup-normalized), every
canonical Hodge class lies in the `c`-th power of the span of divisor classes (the first Chern
classes
of line bundles). -/
def HodgeClasses : Prop :=
  ∀ (h : ℕ) (U : UniformizationData (powObj ℂ S.Jℂ.X (h + 1))) (c : ℕ)
    (c₂ : CupComparison (powObj ℂ S.Jℂ.X (h + 1)) 2)
    (cr : CupComparison (powObj ℂ S.Jℂ.X (h + 1)) (2 * c))
    (c1 : Stacks.Picard.ofScheme (powObj ℂ S.Jℂ.X (h + 1)).left →+
      bettiCohomology (powObj ℂ S.Jℂ.X (h + 1)) 2),
    IsBettiFirstChern (U := U) c₂ c1 →
    ∀ x ∈ canonicalHodgeClasses U cr,
      ((cr.toEquiv.symm x : ⋀[ℚ]^(2 * c) (bettiCohomology (powObj ℂ S.Jℂ.X (h + 1)) 1)) :
        ExteriorAlgebra ℚ (bettiCohomology (powObj ℂ S.Jℂ.X (h + 1)) 1)) ∈
        divisorProductSpan c₂ c1 c

/-- **Surjectivity of the cycle class map** (Corollary 6.6): for every number field `K ⊂ ℚ̄`, prime
`ℓ`, `h ≥ 1` and `c ≥ 0`, the `ℚ_ℓ`-span of the (canonical) cycle classes of `CH^c((J_f^h)_K)` is
the
whole of `H^{2c}_ét((J_f^h)_{ℚ̄}, ℚ_ℓ(c))^{Gal(ℚ̄/K)}`. `(J_f^h)_K` is any pullback `X` of `J_f^h`
along `Spec K ⟶ Spec ℚ` in a big étale site; `i = h·dim J_f - c` is the Chow dimension. -/
def CycleClasses (Canon : CycleClassPredicate) : Prop :=
  ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (h c : ℕ) (i : ℤ)
    (_ : i + c = (((h + 1) * ((f.natDegree - 1) / 2) : ℕ) : ℤ))
    (B' : BigEtaleSite.{0}) [EllAdicSite B' ℓ] (X : B'.Scheme) [IsNoetherian X.1]
    (fX : X.1 ⟶ Spec (.of E)) [IsProper fX] (π : X.1 ⟶ (powObj ℚ S.J.X (h + 1)).left)
    (_ : IsPullback π fX (powObj ℚ S.J.X (h + 1)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ E))))
    (F : CycleClassFunctoriality B' ℓ X fX (AlgebraicClosure ℚ) c i)
    (_ : Canon B' ℓ X fX (AlgebraicClosure ℚ) c i F),
    Submodule.span ℚ_[ℓ] (Set.range F.clBase) =
      (etaleCohomologyTwistRep B' ℓ X fX (AlgebraicClosure ℚ) c).invariants

/-- **The Hodge conjecture for every power `J_f^h`** (Corollary 6.6): every rational Hodge class in
`H^{2c}(J_f^h(ℂ), ℚ)` lies in the `ℚ`-span of the classes of algebraic cycles, for every
Betti cycle class system with the cited properties (cycle classes are Hodge classes and
contain products of
divisor classes). `i = h·dim J_f - c` is the Chow dimension. -/
def HodgeConjecture : Prop :=
  ∀ (h : ℕ) [LocallyOfFiniteType (powObj ℂ S.Jℂ.X (h + 1)).hom]
    (U : UniformizationData (powObj ℂ S.Jℂ.X (h + 1))) (c : ℕ)
    (c₂ : CupComparison (powObj ℂ S.Jℂ.X (h + 1)) 2)
    (cr : CupComparison (powObj ℂ S.Jℂ.X (h + 1)) (2 * c))
    (c1 : Stacks.Picard.ofScheme (powObj ℂ S.Jℂ.X (h + 1)).left →+
      bettiCohomology (powObj ℂ S.Jℂ.X (h + 1)) 2)
    (_ : IsBettiFirstChern (U := U) c₂ c1) (i : ℤ)
    (_ : i + c = (Stacks.Groupoids.abelianVarietyDimension
      (powObj ℂ S.Jℂ.X (h + 1)) : ℤ))
    (Sys : BettiCycleClassSystem U c₂ c1 c cr i),
    canonicalHodgeClasses U cr ≤ Submodule.span ℚ (Set.range Sys.cl)

/-- The canonical first homology of each positive power identifies its Mumford–Tate group
with the diagonal Mumford–Tate group of `J_f`. This states the group comparison on the
Betti spaces, independently of the chosen uniformizations. -/
def MumfordTatePowerGroups : Prop :=
  ∀ (U : UniformizationData S.Jℂ.X)
    (D : ∀ h, UniformizationData (powObj ℂ S.Jℂ.X (h + 1))) (h : ℕ),
    (D h).canonicalHodge.mumfordTateGroup =
      (U.canonicalHodge.mumfordTateGroup.map
        (ArithmeticOfJacobiPolynomials.diagHom ℚ (Fin (h + 1)) (bettiOne S.Jℂ.X))).map
          (hodgeAutCongr (bettiPowEquiv S.Jℂ.X U D h).symm).toMonoidHom

/-- **The Mumford–Tate conjecture for `J_f` and every positive power** (Corollary 6.6),
in the canonical direct-sum coordinates on Betti and Tate homology. The first conjunct identifies
`MT(J_f^{h+1})` with diagonal `MT(J_f)` on the Betti space. The second gives the
corresponding Lie equality on the Tate module of `J_f^r`, using `powEquivPi` to express
it in direct-sum coordinates. Only the single-Jacobian equality is a cited input; finite
extensions and powers are transferred by the manuscript's own argument. -/
def MumfordTateConjecture : Prop :=
  S.MumfordTatePowerGroups ∧
  ∀ (σ : AlgebraicClosure ℚ →ₐ[ℚ] ℂ)
    (emb : S.Jℂ.X.left ⟶ S.J.X.left)
    (_ : IsPullback emb S.Jℂ.X.hom S.J.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
    (_ : PreservesOrigin emb) (U : UniformizationData S.Jℂ.X) (ℓ : ℕ) [Fact ℓ.Prime] {n : ℕ}
    (bV : Module.Basis (Fin n) ℚ (bettiOne S.Jℂ.X))
    (bW : Module.Basis (Fin n) ℚ_[ℓ]
      (rationalTate ℓ (GeomPoints ℚ (AlgebraicClosure ℚ) S.J.X)))
    (_ : IsBettiTateComparison U emb σ ℓ bV bW)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
    (r : ℕ) [NeZero r],
    ellAdicLie ℓ (E.fixingSubgroup.map (powTateUnits bW r)) =
      AbelianTateLie.diagHom (ℓ := ℓ) (W := Fin n → ℚ_[ℓ]) r ''
        (Submodule.span ℚ_[ℓ]
          (liftEnd ℓ bV '' zariskiLie bV U.canonicalHodge.mumfordTateGroup) : Set _)

/-- Uniformizations, cup comparisons, first-Chern maps and Betti cycle
systems exist on every power, in every codimension. The Chow dimension is the
geometric dimension minus the codimension. -/
def HodgeCycleData : Prop :=
  letI := S.isJacobianℂ.isAbelianVariety
  ∀ (h c : ℕ),
    ∃ (U : UniformizationData (powObj ℂ S.Jℂ.X (h + 1)))
      (c₂ : CupComparison (powObj ℂ S.Jℂ.X (h + 1)) 2)
      (cr : CupComparison (powObj ℂ S.Jℂ.X (h + 1)) (2 * c))
      (c1 : Stacks.Picard.ofScheme (powObj ℂ S.Jℂ.X (h + 1)).left →+
        bettiCohomology (powObj ℂ S.Jℂ.X (h + 1)) 2),
      IsBettiFirstChern (U := U) c₂ c1 ∧
      Nonempty (BettiCycleClassSystem U c₂ c1 c cr
        ((Stacks.Groupoids.abelianVarietyDimension
          (powObj ℂ S.Jℂ.X (h + 1)) : ℤ) - c))

/-- For every complex base change, uniformization and rational basis,
the canonically characterized Betti–Tate comparison has a Tate basis witness. -/
def BettiTateComparisonData : Prop :=
  ∀ (σ : AlgebraicClosure ℚ →ₐ[ℚ] ℂ)
    (emb : S.Jℂ.X.left ⟶ S.J.X.left)
    (_ : IsPullback emb S.Jℂ.X.hom S.J.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
    (_ : PreservesOrigin emb) (U : UniformizationData S.Jℂ.X) (ℓ : ℕ) [Fact ℓ.Prime] {n : ℕ}
    (bV : Module.Basis (Fin n) ℚ (bettiOne S.Jℂ.X)),
    ∃ bW : Module.Basis (Fin n) ℚ_[ℓ]
      (rationalTate ℓ (GeomPoints ℚ (AlgebraicClosure ℚ) S.J.X)),
      IsBettiTateComparison U emb σ ℓ bV bW

/-- **Corollary 6.6**, the entire conclusion, for a Jacobian `J_f` of the curve
`y² = f(x)` in the setting `S`, relative to the canonical cycle class predicate `Canon`. The last
conjunct is the concluding sentence: the Hodge, Tate (`CycleClasses` over every number field) and
Mumford–Tate conjectures for all positive powers. -/
def ArithmeticConclusions (Canon : CycleClassPredicate) : Prop :=
  S.Dimension ∧ S.EndomorphismRing ∧ S.HodgeGroupData ∧ S.HodgeGroups ∧ S.TateLie ∧
    S.HodgeClasses ∧ S.CycleClasses Canon ∧
    (S.HodgeConjecture ∧ S.CycleClasses Canon ∧ S.MumfordTateConjecture)

end JacobianSetting

/-! ### The manuscript's derivation from the cited inputs -/

namespace JacobianSetting

variable {f : ℚ[X]} (S : JacobianSetting f)

open AbelianBettiHodge AbelianBettiCohomology AbelianHodgeClasses AbelianArithmetic
  AbelianEtale AbelianCycleClass ComplexRealization

/-- **`dim J_f = ⌊(d - 1)/2⌋`**: Stacks' genus theorem and the proved hyperelliptic genus
formula. -/
theorem dimension (hf : f.Separable) (hd : 0 < f.natDegree) : S.Dimension :=
  Jacobian.abelianVarietyDimension_hyperelliptic (K := AlgebraicClosure ℚ) (by norm_num) hf hd
    S.B S.hC S.hQ S.hL S.hCL S.g S.hg S.gL S.hgL S.isJacobian

/-- **`End_{ℚ̄}(J_f) = ℤ`**: Zarhin Theorem 2.4. -/
theorem endomorphismRing (hEnd : Zarhin.GeometricEndomorphisms.{0}) (hf : f.Separable)
    (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) : S.EndomorphismRing :=
  jacobianEndomorphismRing_of_symmetric hEnd hf hd hS S.B S.hCL S.hL S.gL S.hgL S.hdimL S.JL
    S.isJacobianL

/-- **The canonical principal polarization and its Riemann form exist** on the complex Jacobian. -/
theorem hodgeGroupData (hCanon : Jacobian.CanonicalPrincipalPolarizationExists.{0})
    (hUnif : AbelianBettiHodge.ComplexUniformization)
    (hRiem : AbelianBettiHodge.PolarizationRiemannForm) (hf : f.Separable)
    (hd : 0 < f.natDegree) : S.HodgeGroupData := by
  have hdℂ : 0 < (f.map (algebraMap ℚ ℂ)).natDegree := by
    rw [Polynomial.natDegree_map]; exact hd
  obtain ⟨D, P, φ, hφ, hCan⟩ := jacobianCanonicalPolarization_hyperelliptic hCanon
    (k := ℂ) (f := f.map (algebraMap ℚ ℂ)) (by norm_num) hf.map hdℂ S.B S.hCℂ S.hℂ S.gℂ S.hgℂ
    S.hdimℂ S.Jℂ S.isJacobianℂ
  have := S.isJacobianℂ.isAbelianVariety
  obtain ⟨U⟩ := hUnif S.Jℂ.X
  obtain ⟨hP⟩ := hCan.poincare
  exact ⟨D, P, φ, hφ, hCan, U, hRiem S.Jℂ.X U D.X P hP φ hCan.principal.isPolarization⟩

/-- **`Hdg(J_f) = Sp(V, ψ)` and `MT(J_f) = GSp(V, ψ)`**: Zarhin Theorem 9.1 proof / Remark 9.2. -/
theorem hodgeGroups (hZ : Zarhin.HodgeAndMumfordTateGroups) (hf : f.Separable)
    (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) : S.HodgeGroups := by
  intro D _ P φ _ hCan U F
  exact jacobianHodgeGroups_hyperelliptic hZ hf hd (Zarhin.admissibleGalois_of_symmetric hS)
    S.B S.hCℂ S.hℂ S.gℂ S.hgℂ S.hdimℂ S.Jℂ S.isJacobianℂ D P φ hCan U F

set_option maxHeartbeats 1000000 in
-- The canonical Jacobian, Weil pairing and Tate-module transports exceed the default budget.
/-- **The `ℓ`-adic Lie algebra**: Zarhin Theorem 2.6 over `ℚ`, the Weil pairing facts, and the
manuscript's finite-index and diagonal-power transfers. -/
theorem tateLie (hCanon : Jacobian.CanonicalPrincipalPolarizationExists.{0})
    (hExist : AbelianVariety.WeilPairingsExist.{0})
    (hAlt : AbelianVariety.PolarizedWeilAlternating.{0}) (hZarhin : Zarhin.TateLieAlgebra.{0})
    (hf : f.Separable) (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) : S.TateLie := by
  refine ⟨?_, ?_, ?_⟩
  · exact jacobianCanonicalPolarization_hyperelliptic hCanon (by norm_num) hf (by omega) S.B
      S.hC S.hQ S.g S.hg S.hdim S.J S.isJacobian
  · intro D _ _ P φ _ hCan ℓ _
    have := S.isJacobian.isAbelianVariety
    obtain ⟨W, hWeil, hWA, hWP⟩ := hCan.exists_weilPairing (L := AlgebraicClosure ℚ) hExist hAlt ℓ
      (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero)
    exact ⟨W, hWeil, hWA, hWP⟩
  · intro D _ _ P φ _ hCan ℓ _ W hWeil m b E _ r _
    exact jacobianTateLie_of_symmetric hZarhin hf hd hS S.B S.hC S.hQ S.g S.hg S.hdim S.J
      S.isJacobian D P φ hCan ℓ W hWeil m b E r

/-- **Rational Hodge classes on every power are combinations of divisor products**:
Zarhin Theorem 9.1. -/
theorem hodgeClasses (hZ : JacobianArithmeticInputs.HodgeClassDivisorProducts) (hf : f.Separable)
    (hd : 5 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) : S.HodgeClasses := by
  intro h U c c₂ cr c1 hc1 x hx
  exact hZ ℚ f hf hd (Zarhin.admissibleGalois_of_symmetric hS) _
    (Zarhin.hyperellipticModel_projectiveModel (by norm_num) hf.map
      (by rw [Polynomial.natDegree_map]; omega))
    S.B S.hCℂ S.hℂ S.gℂ S.hgℂ S.hdimℂ S.Jℂ S.isJacobianℂ h U c c₂ cr c1 hc1 x hx

/-- **The Hodge conjecture for every power**: the manuscript's step *Hodge classes are combinations
of products of divisor classes, which are algebraic*. -/
theorem hodgeConjecture (hHC : S.HodgeClasses) : S.HodgeConjecture := by
  intro h _ U c c₂ cr c1 hc1 i hi Sys x hx
  have hmem := hHC h U c c₂ cr c1 hc1 x hx
  obtain ⟨z, hz, hzx⟩ := Sys.divisor_products _ hmem
  have : z = x := by
    have h1 : (cr.toEquiv.symm z : ⋀[ℚ]^(2 * c) (bettiCohomology (powObj ℂ S.Jℂ.X (h + 1)) 1)) =
        cr.toEquiv.symm x := Subtype.ext hzx
    exact cr.toEquiv.symm.injective h1
  exact this ▸ hz

/-- **The Mumford–Tate conjecture for every power** (Corollary 6.6): Zarhin Remark 9.2 over `ℚ`
(`MumfordTateLieEquality`) and the manuscript's finite-index passage to a number field `E`. -/
theorem mumfordTateConjecture (hMT : JacobianArithmeticInputs.MumfordTateLieEquality)
    (hf : f.Separable)
    (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) : S.MumfordTateConjecture := by
  have := S.isJacobian.isAbelianVariety
  have := S.isJacobianℂ.isAbelianVariety
  refine ⟨?_, ?_⟩
  · intro U D h
    exact UniformizationData.mumfordTateGroup_bettiPow S.Jℂ.X U D h
  · intro σ emb hemb h0 U ℓ _ n bV bW hcomp E _ r _
    have hℓ : (ℓ : AlgebraicClosure ℚ) ≠ 0 := natCast_ne_zero_algebraicClosure_rat ℓ
    have hrange := hMT ℚ (AlgebraicClosure ℚ) σ f hf hd
      (Zarhin.admissibleGalois_of_symmetric hS) (Over.mk (Hyperelliptic.toSpecField f))
      (Zarhin.hyperellipticModel_projectiveModel (by norm_num) hf (by omega))
      S.B S.hC S.hQ S.g S.hg S.hdim S.J S.isJacobian S.Jℂ emb hemb h0 U ℓ bV bW hcomp
    exact AbelianTateLie.ellAdicLie_fixingSubgroup_map_powTateUnits_eq bW (r := r) hrange hℓ E

/-- The general cited background supplies realized Betti cycle data in every
codimension on every power. -/
theorem hodgeCycleData (hUnif : AbelianBettiHodge.ComplexUniformization)
    (hCup : TorusBettiCupProduct)
    (hChern : BettiFirstChernExists)
    (hCycle : AbelianArithmetic.BettiCycleClassExists) : S.HodgeCycleData := by
  have := S.isJacobianℂ.isAbelianVariety
  intro h c
  let A := powObj ℂ S.Jℂ.X (h + 1)
  obtain ⟨U⟩ := hUnif A
  obtain ⟨c₂⟩ := exists_bettiCupComparison hCup A U 2
  obtain ⟨cr⟩ := exists_bettiCupComparison hCup A U (2 * c)
  obtain ⟨c1, hc1⟩ := hChern A U c₂
  exact ⟨U, c₂, cr, c1, hc1,
    hCycle A U c₂ c1 hc1 c cr
      ((Stacks.Groupoids.abelianVarietyDimension A : ℤ) - c) (by omega)⟩

/-- The period–torsion comparison provides a witness on every
base change of the manuscript's Jacobian. -/
theorem bettiTateComparisonData (hComp : AbelianArithmetic.BettiTateComparisonExists) :
    S.BettiTateComparisonData := by
  have := S.isJacobian.isAbelianVariety
  have := S.isJacobianℂ.isAbelianVariety
  intro σ emb hemb h0 U ℓ _ n bV
  exact hComp ℚ (AlgebraicClosure ℚ) σ S.J.X S.Jℂ.X emb hemb h0 U ℓ bV

/-- **Corollary 6.6 assembled**, from the general cited inputs and the cycle class
conjunct `hCycle`, which is the Tate-class statement `Zarhin.TateClassesDivisorProducts`
(Theorem 8.1) reduced by averaging over a finite Galois extension in the curves interface (its
instance `cycleClasses_rat`). Dimension,
endomorphisms, Hodge/Mumford–Tate groups, the `ℓ`-adic Lie algebra, Hodge classes and the Hodge and
Mumford–Tate conjectures are derived here. -/
theorem arithmeticConclusions_of_cycleClasses (Canon : CycleClassPredicate)
    (hEnd : Zarhin.GeometricEndomorphisms.{0})
    (hCanon : Jacobian.CanonicalPrincipalPolarizationExists.{0})
    (hUnif : AbelianBettiHodge.ComplexUniformization)
    (hRiem : AbelianBettiHodge.PolarizationRiemannForm)
    (hHM : Zarhin.HodgeAndMumfordTateGroups)
    (hExist : AbelianVariety.WeilPairingsExist.{0})
    (hAlt : AbelianVariety.PolarizedWeilAlternating.{0}) (hTate : Zarhin.TateLieAlgebra.{0})
    (hHC : JacobianArithmeticInputs.HodgeClassDivisorProducts)
    (hMT : JacobianArithmeticInputs.MumfordTateLieEquality)
    (hf : f.Separable) (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f)
    (hCycle : S.CycleClasses Canon) : S.ArithmeticConclusions Canon :=
  have hHodge := S.hodgeClasses hHC hf (by omega) hS
  ⟨S.dimension hf (by omega), S.endomorphismRing hEnd hf hd hS,
    S.hodgeGroupData hCanon hUnif hRiem hf (by omega), S.hodgeGroups hHM hf hd hS,
    S.tateLie hCanon hExist hAlt hTate hf hd hS, hHodge, hCycle,
    S.hodgeConjecture hHodge, hCycle, S.mumfordTateConjecture hMT hf hd hS⟩

end JacobianSetting

end ArithmeticOfJacobiPolynomials

end
