/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBaseChange
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticGenusComparison
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticCurve
public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.AlgClosed
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChangeGeneral
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Unconditional
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# The hyperelliptic curve is a smooth projective curve in the sense of the Stacks library

Let `K` be a field with `2 ≠ 0` and `f ∈ K[x]` separable of degree `d ≥ 1`, and let
`X = projectiveModel f` be the smooth projective model of `y² = f(x)` built in
`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective`. This file shows that `X → Spec K`
satisfies the
hypotheses of the Stacks theory of the Picard scheme and the Jacobian of a curve
(`Stacks.PicardFunctor`, [Stacks, Tags 0B9Z, 0BA0, 0C1Z]):

* `ArithmeticOfJacobiPolynomials.Hyperelliptic.isCurve_toSpecField`: `IsCurve K (toSpecField f)`;
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.isProjectiveVariety_toSpecField`:
`IsProjectiveVariety K
  (toSpecField f)` (a proper curve over a field is projective, Stacks'
  `isProjectiveMorphism_of_isProper_of_isCurve`);
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.geometricallyIrreducible_toSpecField`;
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.genus_toSpecField`: Stacks'
`AlgebraicGeometry.genus` of the model
  is `⌊(d - 1)/2⌋` (the genus comparison `genus_projectiveModel`).

Over an algebraically closed `K` the Stacks theorems then apply to the model:

* `ArithmeticOfJacobiPolynomials.Hyperelliptic.exists_jacobian`: there is an abelian variety `J`
over `K` of
  dimension `⌊(d - 1)/2⌋` with `J(K) ≃+ Pic⁰(X)` ([Stacks, Tag 0BA0]);
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.nonempty_torsionBy_addEquiv_pi_zmod`: for `n ≥ 1`
invertible in `K`,
  `Pic(X)[n] ≃+ (ℤ/n)^{2⌊(d - 1)/2⌋}` ([Stacks, Tag 0C1Z], clause (1)).

* `ArithmeticOfJacobiPolynomials.Hyperelliptic.exists_section_of_isSepClosed`: over a separably
closed field the
  model has a rational point (so the Stacks construction with a chosen point applies);
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.exists_isJacobianOf_of_isAlgClosed`: over an
algebraically closed
  field the model has a Jacobian in the sense of
  `ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf` (which
  does not mention a rational point), of dimension `⌊(d - 1)/2⌋`;

Nothing here is specific to a particular `f`: the genus and curve properties are proved for this
model, and the Jacobian statements are the Stacks theorems instantiated at it.
-/

public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Polynomial

open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

variable {K : Type u} [Field K] {f : K[X]}

/-- **The hyperelliptic model is a curve** ([Stacks, Tag 0BY7] et seq.): an integral, separated,
quasi-compact, locally of finite type `K`-scheme of dimension one. -/
theorem isCurve_toSpecField (h2 : (2 : K) ≠ 0) (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    IsCurve K (toSpecField f) := by
  obtain ⟨-, hproper, hint, hdim⟩ := projectiveModel_curve h2 hf hdeg
  have := hint
  have := hproper
  exact { toIsIntegral := hint, topologicalKrullDim_eq_one := hdim }

/-- The hyperelliptic model is geometrically irreducible over `K`. -/
theorem geometricallyIrreducible_toSpecField (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    GeometricallyIrreducible (toSpecField f) := by
  have := geometricallyIntegral_toSpecField hf hdeg
  infer_instance

/-- **The hyperelliptic model is a projective variety** (a proper curve over a field is
projective, Stacks' `isProjectiveMorphism_of_isProper_of_isCurve`). -/
theorem isProjectiveVariety_toSpecField (h2 : (2 : K) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) : IsProjectiveVariety K (toSpecField f) := by
  have := isCurve_toSpecField h2 hf hdeg
  have := isProper_toSpecField f
  exact (isProjectiveVariety_iff K _).2
    ⟨inferInstance, isProjectiveMorphism_of_isProper_of_isCurve K _⟩

/-- **The genus of the hyperelliptic model** in the sense of the Stacks library
(`dim_K H¹(X, 𝒪_X)`, Tag 0BY7) is `⌊(deg f - 1)/2⌋`. -/
theorem genus_toSpecField : AlgebraicGeometry.genus (toSpecField f) = (f.natDegree - 1) / 2 :=
  genus_projectiveModel f

section AlgClosed

variable [IsAlgClosed K]

/-- **The Jacobian of the hyperelliptic curve over an algebraically closed field** ([Stacks,
Tag 0BA0]): an abelian variety `J` of dimension `⌊(deg f - 1)/2⌋` whose group of `K`-points is
`Pic⁰(X)`. -/
theorem exists_jacobian (h2 : (2 : K) ≠ 0) (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    ∃ (J : Over (Spec (CommRingCat.of K))) (_ : GrpObj J) (_ : IsAbelianVariety K J),
      (Stacks.Groupoids.abelianVarietyDimension J : ℕ) = (f.natDegree - 1) / 2 ∧
      letI : IsCommMonObj J := isCommMonObj_of_isProper_of_geometricallyIntegral J
      haveI : IsCurve K (toSpecField f) := isCurve_toSpecField h2 hf hdeg
      haveI : IsProper (toSpecField f) := isProper_toSpecField f
      Nonempty (Stacks.Picard.ofSchemeDegreeZero K (toSpecField f)
        (IsCurve.topologicalKrullDim_eq_one (k := K) (f := toSpecField f)).le
        ≃+ Additive (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ J)) := by
  have := isCurve_toSpecField h2 hf hdeg
  have := isProjectiveVariety_toSpecField h2 hf hdeg
  have := (projectiveModel_curve h2 hf hdeg).1
  obtain ⟨J, i, hJ, hdim, e⟩ := Stacks.Picard.exists_jacobian K (toSpecField f)
  exact ⟨J, i, hJ, hdim.trans genus_toSpecField, e⟩

/-- **`Pic(X)[n] ≃ (ℤ/n)^{2g}`** for the hyperelliptic curve `X` of genus `g = ⌊(deg f - 1)/2⌋`
over an algebraically closed field, for `n ≥ 1` invertible in the field ([Stacks, Tag 0C1Z],
clause (1)). -/
theorem nonempty_torsionBy_addEquiv_pi_zmod (h2 : (2 : K) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (n : ℕ) (hn : 1 ≤ n) (hnK : IsUnit (n : K)) :
    Nonempty (Submodule.torsionBy ℤ (Stacks.Picard.ofScheme (projectiveModel f)) (n : ℤ) ≃+
      (Fin (2 * ((f.natDegree - 1) / 2)) → ZMod n)) := by
  have := isCurve_toSpecField h2 hf hdeg
  have := isProjectiveVariety_toSpecField h2 hf hdeg
  have := (projectiveModel_curve h2 hf hdeg).1
  have h := Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve K
    (toSpecField f) n hn hnK
  rwa [genus_toSpecField] at h

/-- The sheaf-theoretic Jacobian of the model over an algebraically closed field: for every big
fppf site `B` containing the model and `Spec K`, with `g` the structure morphism, the Stacks
construction ([Stacks, Tags 0B9Z, 0BA0]) gives a group scheme `G` representing `Pic⁰_{X/K}` which
is an abelian variety of dimension `⌊(deg f - 1)/2⌋`. -/
theorem exists_isJacobianOf_of_isAlgClosed (h2 : (2 : K) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (B : BigFppfSite.{u}) (hX : B.Contains (projectiveModel f))
    (hk : B.Contains (Spec (CommRingCat.of K))) (g : B.obj hX ⟶ B.obj hk)
    (hg : B.inclusion.map g = toSpecField f) :
    haveI : IsCurve K (toSpecField f) := isCurve_toSpecField h2 hf hdeg
    haveI : IsProper (B.inclusion.map g) := by rw [hg]; exact isProper_toSpecField f
    ∃ G : Grp (Over (Spec (CommRingCat.of K))),
      Nonempty (Jacobian.IsJacobianOf B hX hk g
        (IsCurve.topologicalKrullDim_eq_one (k := K) (f := toSpecField f)).le G) ∧
        Stacks.Groupoids.abelianVarietyDimension G.X = (f.natDegree - 1) / 2 := by
  have hc : IsCurve K (B.inclusion.map g) := by rw [hg]; exact isCurve_toSpecField h2 hf hdeg
  have hp : IsProjectiveVariety K (B.inclusion.map g) := by
    rw [hg]; exact isProjectiveVariety_toSpecField h2 hf hdeg
  have hs : Smooth (B.inclusion.map g) := by rw [hg]; exact smooth_toSpecField h2 hf hdeg
  obtain ⟨G, hG, hdim⟩ := Jacobian.exists_isJacobianOf_of_isAlgClosed B hX K g
  refine ⟨G, hG, ?_⟩
  rw [hdim, hg, genus_toSpecField]

end AlgClosed

/-- **The hyperelliptic model has a rational point over a separably closed field** (a smooth
curve over a separably closed field has a rational point, [Stacks, Tag 056U]; used to cut out
`Pic⁰` in the Stacks construction with a chosen point). -/
theorem exists_section_of_isSepClosed [IsSepClosed K] (h2 : (2 : K) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) :
    ∃ σ : Spec (CommRingCat.of K) ⟶ projectiveModel f, σ ≫ toSpecField f = 𝟙 _ := by
  have := smooth_toSpecField h2 hf hdeg
  have := (projectiveModel_curve h2 hf hdeg).2.2.1
  obtain ⟨σ, hσ, -⟩ := AlgebraicGeometry.exists_section_of_isSepClosed (toSpecField f)
  exact ⟨σ, hσ⟩

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
