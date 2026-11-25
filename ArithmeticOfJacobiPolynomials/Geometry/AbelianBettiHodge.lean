/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.ComplexRealizationFunctor
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianVariety
public import ArithmeticOfJacobiPolynomials.Algebra.HodgeStructure
public import ArithmeticOfJacobiPolynomials.Algebra.HodgeGroupPower
public import ArithmeticOfJacobiPolynomials.Geometry.GroupSchemeProduct
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Functorial
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentProduct
import all ArithmeticOfJacobiPolynomials.Algebra.ComplexRealization
import all ArithmeticOfJacobiPolynomials.Algebra.ComplexRealizationFunctor
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The Betti space of an abelian variety and its canonical Hodge structure

Manuscript, Corollary 6.6: `V = H₁(J(ℂ), ℚ)` is the singular homology of
the analytic space of complex points
(`ArithmeticOfJacobiPolynomials.ComplexRealization.bettiOne`, functorial in morphisms by
`ArithmeticOfJacobiPolynomials.ComplexRealization.bettiFunctor`), and `Hdg`, `MT` are taken with
respect to the
**canonical** weight `-1` Hodge structure of the complex abelian variety.

## What pins the Hodge structure to the complex geometry

For a group scheme `A` over `ℂ`:

* `TangentAt A σ` **is** the Stacks tangent space `AlgebraicGeometry.DottedTangentArrow A.hom x`
  (Stacks tag 0B2C) at the point `x` underlying a complex point `σ`; its `ℂ`-vector space
  structure is the canonical `κ(x)`-structure of Stacks transported along the canonical residue
  field identification `AlgebraicGeometry.sectionResidueFieldEquiv : κ(x) ≃+* ℂ`. `Lie A` is the
  tangent space at the identity. The only local
  definitions are the *evaluation bridges* (`tangentEval`, `ptEval`), which evaluate the Stacks
  derivation (`dottedDerivationEquiv`) on the germ of a regular function and transfer the
  value in `κ(x)` to `ℂ` by the canonical identification. The topology of `Lie A` is induced by
  these evaluations.
* `IsOneParameter A v φ` says that `φ : ℂ → A(ℂ)` is a continuous homomorphism for the analytic
  topology whose derivative at `0` along every regular function `s` is the evaluation of `v` on `s`;
  `IsExp A E` says `t ↦ E (t • v)` is that subgroup, i.e. `E = exp`.
* `IsUniformizingIso A E ψ` says `ψ : ℝ ⊗ H₁(A(ℂ), ℚ) ≃ Lie A` sends the singular homology class
  `loopClass σ` of a closed singular `1`-simplex to the displacement of its lift along `E`.
* `UniformizationData A` bundles, **for one object**, `exp`, `period` and the geometric conditions
  that characterize them. The general existence statement is in `External.lean`.
  `canonicalHodge D` is *defined* from `D`: its `J` is `i` on `Lie A` transported through the period
  isomorphism. Independence of the chosen data (`UniformizationData.J_eq`) is proved from the
  uniqueness conditions.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial TensorProduct
open Convexity

namespace ArithmeticOfJacobiPolynomials.AbelianBettiHodge

open ArithmeticOfJacobiPolynomials.ComplexRealization

/-- The homology class of a closed singular `1`-simplex, with `ℚ` coefficients. -/
def simplexClassAux (Y : SSet.{0}) (x : Y _⦋1⦌) (h : Y.δ 0 x = Y.δ 1 x) :
    ModuleCat.of ℚ ℚ ⟶ Y.homology (ModuleCat.of ℚ ℚ) 1 :=
  (Y.chainComplex (ModuleCat.of ℚ ℚ)).liftCycles (Y.ιChainComplex x) 0
    (ChainComplex.next_nat_succ 0) (by simp [h]) ≫
    (Y.chainComplex (ModuleCat.of ℚ ℚ)).homologyπ 1

/-- Naturality of the class of a closed simplex under maps of simplicial sets. -/
theorem simplexClassAux_naturality {Y Y' : SSet.{0}} (g : Y ⟶ Y') (x : Y _⦋1⦌)
    (h : Y.δ 0 x = Y.δ 1 x) :
    simplexClassAux Y x h ≫ SSet.homologyMap g (ModuleCat.of ℚ ℚ) 1 =
      simplexClassAux Y' (g.app _ x) (by
        have := congrArg (g.app _) h
        simpa [← SSet.δ_naturality_apply] using this) := by
  unfold simplexClassAux
  simp only [SSet.homologyMap]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono ((Y'.chainComplex (ModuleCat.of ℚ ℚ)).iCycles 1)]
  simp

/-- The class in `H₁(X(ℂ), ℚ)` of a closed singular `1`-simplex of the analytic space of complex
points of `A`. -/
def loopClass (A : Over (Spec (CommRingCat.of ℂ)))
    (σ : (TopCat.toSSet.obj (space A)) _⦋1⦌)
    (h : (TopCat.toSSet.obj (space A)).δ 0 σ = (TopCat.toSSet.obj (space A)).δ 1 σ) :
    bettiOne A :=
  (simplexClassAux _ σ h).hom 1

/-! ### Tangent spaces at complex points: the Stacks construction -/

open scoped CategoryTheory.MonObj
open IsLocalRing

/-- The category of schemes over `Spec ℂ`. -/
abbrev CSch : Type 1 := Over (Spec (CommRingCat.of ℂ))

section Tangent

variable {A : CSch}

/-- The morphism `Spec ℂ ⟶ A` underlying a complex point. -/
abbrev secLeft (σ : Points A) : Spec (CommRingCat.of ℂ) ⟶ A.left := σ.left

/-- The scheme point underlying a complex point. -/
abbrev secPt (σ : Points A) : A.left := secLeft σ (closedPoint ℂ)

theorem secLeft_comp (σ : Points A) : secLeft σ ≫ A.hom = 𝟙 _ := by
  simp

/-- The canonical identification of the residue field at a complex point with `ℂ`
(`AlgebraicGeometry.sectionResidueFieldEquiv`). -/
abbrev resEquiv (σ : Points A) : A.left.residueField (secPt σ) ≃+* ℂ :=
  sectionResidueFieldEquiv A.hom (secLeft σ) (secLeft_comp σ)

variable (A) in
/-- **The tangent space of `A` at the complex point `σ`**: the Stacks tangent space
`AlgebraicGeometry.DottedTangentArrow` of the structure morphism at the underlying point
(Stacks 0B2C). -/
@[expose] def TangentAt (σ : Points A) : Type := DottedTangentArrow A.hom (secPt σ)

instance (σ : Points A) : AddCommGroup (TangentAt A σ) :=
  inferInstanceAs (AddCommGroup (DottedTangentArrow A.hom (secPt σ)))

/-- The `ℂ`-vector space structure: the canonical `κ(x)`-structure of Stacks transported along the
canonical identification `κ(x) ≃ ℂ`. -/
instance (σ : Points A) : Module ℂ (TangentAt A σ) :=
  Module.compHom (DottedTangentArrow A.hom (secPt σ)) (resEquiv σ).symm.toRingHom

theorem smul_eq (σ : Points A) (c : ℂ) (θ : TangentAt A σ) :
    c • θ = (show DottedTangentArrow A.hom (secPt σ) from ((resEquiv σ).symm c •
      (show DottedTangentArrow A.hom (secPt σ) from θ))) := rfl

/-- **Evaluation bridge.** The value of a tangent vector on (the germ at the base point of) a
regular function `s` defined near the point: the Stacks derivation `dottedDerivationEquiv`,
evaluated on the germ, transferred from `κ(x)` to `ℂ` by the canonical identification. -/
def tangentEval {σ : Points A} (v : TangentAt A σ) (U : A.left.Opens) (hU : secPt σ ∈ U)
    (s : Γ(A.left, U)) : ℂ :=
  resEquiv σ ((dottedToDerivation A.hom (secPt σ)
    (show DottedTangentArrow A.hom (secPt σ) from v)).1
      ((A.left.presheaf.germ U (secPt σ) hU).hom s))

/-- The topology of pointwise convergence of the evaluations on regular functions near the base
point (the usual topology of the finite-dimensional `ℂ`-vector space). -/
instance (σ : Points A) : TopologicalSpace (TangentAt A σ) :=
  TopologicalSpace.induced
    (fun (v : TangentAt A σ) (U : {U : A.left.Opens // secPt σ ∈ U}) (s : Γ(A.left, U.1)) =>
      tangentEval v U.1 U.2 s) inferInstance

open Classical in
/-- The value at a complex point `p` of a regular function `s` on an open subscheme `U`
(`0` when `p` lies outside `U`): the germ of `s` at the point, evaluated through the local
homomorphism `stalkClosedPointTo`. -/
@[expose] def ptEval (U : A.left.Opens) (s : Γ(A.left, U)) (p : Points A) : ℂ :=
  if h : secPt p ∈ U then
    (Scheme.stalkClosedPointTo (secLeft p)).hom ((A.left.presheaf.germ U (secPt p) h).hom s)
  else 0

/-- Tangent vectors are determined by their evaluations on regular functions. -/
theorem TangentAt.ext_of_eval {σ : Points A} {v w : TangentAt A σ}
    (h : ∀ (U : A.left.Opens) (hU : secPt σ ∈ U) (s : Γ(A.left, U)),
      tangentEval v U hU s = tangentEval w U hU s) : v = w := by
  have key : dottedToDerivation A.hom (secPt σ) (show DottedTangentArrow A.hom (secPt σ) from v) =
      dottedToDerivation A.hom (secPt σ) (show DottedTangentArrow A.hom (secPt σ) from w) := by
    refine Subtype.ext (Derivation.ext fun a => ?_)
    obtain ⟨U, hU, s, rfl⟩ := A.left.presheaf.exists_germ_eq a
    exact (resEquiv σ).injective (h U hU s)
  have := congrArg (derivationToDotted A.hom (secPt σ)) key
  rwa [derivationToDotted_dottedToDerivation, derivationToDotted_dottedToDerivation] at this

/-- Transport of tangent spaces along an equality of complex points. -/
@[expose] def TangentAt.cast {σ τ : Points A} (h : σ = τ) : TangentAt A σ ≃ₗ[ℂ] TangentAt A τ := by
  subst h
  exact LinearEquiv.refl ℂ _

theorem tangentEval_cast {σ τ : Points A} (h : σ = τ) (v : TangentAt A σ) (U : A.left.Opens)
    (hU : secPt σ ∈ U) (hU' : secPt τ ∈ U) (s : Γ(A.left, U)) :
    tangentEval (TangentAt.cast h v) U hU' s = tangentEval v U hU s := by
  subst h
  rfl

theorem tangentEval_add {σ : Points A} (v w : TangentAt A σ) (U : A.left.Opens)
    (hU : secPt σ ∈ U) (s : Γ(A.left, U)) :
    tangentEval (v + w) U hU s = tangentEval v U hU s + tangentEval w U hU s := by
  unfold tangentEval
  have : dottedToDerivation A.hom (secPt σ)
      (show DottedTangentArrow A.hom (secPt σ) from v + w) =
      dottedToDerivation A.hom (secPt σ) (show DottedTangentArrow A.hom (secPt σ) from v) +
        dottedToDerivation A.hom (secPt σ) (show DottedTangentArrow A.hom (secPt σ) from w) :=
    dottedToDerivation_add _ _ _ _
  rw [this]
  simp

theorem tangentEval_smul {σ : Points A} (c : ℂ) (v : TangentAt A σ) (U : A.left.Opens)
    (hU : secPt σ ∈ U) (s : Γ(A.left, U)) :
    tangentEval (c • v) U hU s = c * tangentEval v U hU s := by
  unfold tangentEval
  rw [smul_eq]
  have := dottedToDerivation_smul A.hom (secPt σ) ((resEquiv σ).symm c)
    (show DottedTangentArrow A.hom (secPt σ) from v)
  rw [this]
  simp

theorem continuous_tangentEval {σ : Points A} (U : A.left.Opens) (hU : secPt σ ∈ U)
    (s : Γ(A.left, U)) : Continuous fun v : TangentAt A σ => tangentEval v U hU s := by
  have c1 : Continuous fun (v : TangentAt A σ) (U : {U : A.left.Opens // secPt σ ∈ U})
      (s : Γ(A.left, U.1)) => tangentEval v U.1 U.2 s := continuous_induced_dom
  exact (continuous_apply s).comp
    ((continuous_apply (⟨U, hU⟩ : {U : A.left.Opens // secPt σ ∈ U})).comp c1)

theorem continuous_of_tangentEval {T : Type*} [TopologicalSpace T] {σ : Points A}
    {f : T → TangentAt A σ}
    (h : ∀ (U : A.left.Opens) (hU : secPt σ ∈ U) (s : Γ(A.left, U)),
      Continuous fun x => tangentEval (f x) U hU s) : Continuous f :=
  continuous_induced_rng.2 (continuous_pi fun U => continuous_pi fun s => h U.1 U.2 s)

end Tangent

section Functorial

variable {A B : CSch} (f : A ⟶ B) (σ : Points A)

/-- The canonical residue field identifications are compatible with `f`. -/
theorem resEquiv_comp (y : B.left.residueField (secPt (σ ≫ f))) :
    resEquiv (σ ≫ f) y = resEquiv σ (f.left.residueFieldMap (secPt σ) y) := by
  simp only [resEquiv, sectionResidueFieldEquiv_apply]
  exact congrArg (fun g => g.hom y)
    (Scheme.descResidueField_stalkClosedPointTo_comp f.left (secLeft σ))

/-- At a complex point the residue field map of a morphism of `ℂ`-schemes is an isomorphism. -/
theorem isIso_residueFieldMap : IsIso (f.left.residueFieldMap (secPt σ)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.left.residueFieldMap (secPt σ)).hom.injective, fun z => ?_⟩
  have h := resEquiv_comp f σ ((resEquiv (σ ≫ f)).symm (resEquiv σ z))
  rw [RingEquiv.apply_symm_apply] at h
  exact ⟨_, ((resEquiv σ).injective h).symm⟩

theorem inv_residueFieldMap_resEquiv_symm [IsIso (f.left.residueFieldMap (secPt σ))] (c : ℂ) :
    (inv (f.left.residueFieldMap (secPt σ))).hom ((resEquiv σ).symm c) =
      (resEquiv (σ ≫ f)).symm c := by
  apply (resEquiv (σ ≫ f)).injective
  rw [RingEquiv.apply_symm_apply]
  have := congrArg (fun g => g.hom ((resEquiv σ).symm c))
    (IsIso.inv_hom_id (f.left.residueFieldMap (secPt σ)))
  simp only [CommRingCat.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  exact (resEquiv_comp f σ _).trans (by rw [this]; simp)

/-- **The tangent map of a morphism at a complex point**: the Stacks tangent map
`AlgebraicGeometry.tangentMap` (tag 0B2F), made `ℂ`-linear by the canonical residue field
identifications. -/
@[expose] def tangentMapAt : TangentAt A σ →ₗ[ℂ] TangentAt B (σ ≫ f) :=
  haveI := isIso_residueFieldMap f σ
  { toFun := fun θ => tangentMap f.left A.hom B.hom (Over.w f) (secPt σ) θ
    map_add' := fun θ θ' => map_add (tangentMap f.left A.hom B.hom (Over.w f) (secPt σ)) θ θ'
    map_smul' := fun c θ => by
      have h := map_smulₛₗ (tangentMap f.left A.hom B.hom (Over.w f) (secPt σ))
        ((resEquiv σ).symm c) (show DottedTangentArrow A.hom (secPt σ) from θ)
      exact h.trans (congrArg
        (fun r : B.left.residueField (f.left (secPt σ)) =>
          r • tangentMap f.left A.hom B.hom (Over.w f) (secPt σ)
            (show DottedTangentArrow A.hom (secPt σ) from θ))
        (inv_residueFieldMap_resEquiv_symm f σ c)) }

/-- `tangentMapAt` is the Stacks tangent map `AlgebraicGeometry.tangentMap` of the underlying
morphism of schemes. -/
theorem tangentMapAt_apply (θ : TangentAt A σ) :
    haveI := isIso_residueFieldMap f σ
    (show DottedTangentArrow B.hom (f.left (secPt σ)) from tangentMapAt f σ θ) =
      tangentMap f.left A.hom B.hom (Over.w f) (secPt σ) θ := rfl

theorem tangentEval_tangentMapAt (v : TangentAt A σ) (U : B.left.Opens)
    (hU : secPt (σ ≫ f) ∈ U) (hU' : secPt σ ∈ f.left ⁻¹ᵁ U) (s : Γ(B.left, U)) :
    tangentEval (tangentMapAt f σ v) U hU s =
      tangentEval v (f.left ⁻¹ᵁ U) hU' (f.left.app U s) := by
  have := isIso_residueFieldMap f σ
  have h1 : dottedToDerivation B.hom (f.left (secPt σ))
      (tangentMap f.left A.hom B.hom (Over.w f) (secPt σ) v) =
      tangentDerivationMap f.left A.hom B.hom (secPt σ) (Over.w f)
        (dottedToDerivation A.hom (secPt σ) v) :=
    dottedToDerivation_derivationToDotted _ _ _
  change resEquiv (σ ≫ f) ((dottedToDerivation B.hom (f.left (secPt σ))
      (tangentMap f.left A.hom B.hom (Over.w f) (secPt σ) v)).1
        ((B.left.presheaf.germ U (f.left (secPt σ)) hU).hom s)) = _
  rw [h1, tangentDerivationMap_val_apply]
  have h2 := Scheme.Hom.germ_stalkMap_apply f.left U (secPt σ) hU s
  rw [h2]
  have := congrArg (fun g => g.hom ((dottedToDerivation A.hom (secPt σ) v).1
    ((A.left.presheaf.germ (f.left ⁻¹ᵁ U) (secPt σ) hU').hom (f.left.app U s))))
    (IsIso.inv_hom_id (f.left.residueFieldMap (secPt σ)))
  simp only [CommRingCat.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  exact (resEquiv_comp f σ _).trans (by rw [this]; rfl)

theorem ptEval_comp (U : B.left.Opens) (s : Γ(B.left, U)) (p : Points A) :
    ptEval U s (p ≫ f) = ptEval (f.left ⁻¹ᵁ U) (f.left.app U s) p := by
  unfold ptEval
  by_cases h : secPt (p ≫ f) ∈ U
  · have h' : secPt p ∈ f.left ⁻¹ᵁ U := h
    simp only [h, h', ↓reduceDIte]
    change (Scheme.stalkClosedPointTo (secLeft p ≫ f.left)).hom _ = _
    rw [Scheme.stalkClosedPointTo_comp]
    exact congrArg (Scheme.stalkClosedPointTo (secLeft p)).hom
      (Scheme.Hom.germ_stalkMap_apply f.left U (secPt p) h s)
  · have h' : secPt p ∉ f.left ⁻¹ᵁ U := h
    simp only [h, h', ↓reduceDIte]

end Functorial

section Lie

variable (A : CSch) [GrpObj A]

/-- **The Lie algebra of `A`**: the Stacks tangent space at the identity point. -/
abbrev Lie : Type := TangentAt A (1 : Points A)

/-- **A one-parameter subgroup with tangent vector `v`**: a continuous homomorphism
`φ : (ℂ, +) → A(ℂ)` (for the analytic topology on `A(ℂ)`) such that, for every regular function `s`
on an open neighbourhood `U` of the identity, `t ↦ s(φ(t))` has complex derivative the evaluation of
`v` on `s` at `t = 0`. -/
structure IsOneParameter (v : Lie A) (φ : ℂ → Points A) : Prop where
  /-- `φ` is a homomorphism. -/
  map_add : ∀ s t, φ (s + t) = φ s * φ t
  /-- `φ` is continuous for the analytic topology. -/
  continuous : @Continuous ℂ (Points A) _ (analyticTopology A) φ
  /-- The derivative at `0` of every regular function along `φ` is the tangent vector. -/
  hasDerivAt : ∀ (U : A.left.Opens) (hU : secPt (1 : Points A) ∈ U) (s : Γ(A.left, U)),
    HasDerivAt (fun t : ℂ => ptEval U s (φ t)) (tangentEval v U hU s) 0

/-- `E : Lie A → A(ℂ)` is an **exponential map**: for every tangent vector `v`, `t ↦ E (t • v)` is
the one-parameter subgroup with tangent vector `v`. -/
def IsExp (E : Lie A → Points A) : Prop :=
  ∀ v : Lie A, IsOneParameter A v (fun t : ℂ => E (t • v))

/-- `lft` is a (continuous) lift of the singular `1`-simplex `σ` of the analytic space `A(ℂ)` along
the map `E : Lie A → A(ℂ)`. -/
def IsLiftOf (E : Lie A → Points A) (σ : (TopCat.toSSet.obj (space A)) _⦋1⦌)
    (lft : C(StdSimplex ℝ (Fin (⦋1⦌.len + 1)), Lie A)) : Prop :=
  ∀ z, E (lft z) = spaceEquiv A (TopCat.toSSetObjEquiv (space A) _ σ z)

/-- `ψ` is a **uniformizing isomorphism** for the exponential map `E`: for every closed singular
`1`-simplex `σ` of the analytic space `A(ℂ)` and every continuous lift `lft` of `σ` to the Lie
algebra (`E ∘ γ = σ`), `ψ` sends the homology class of the loop `σ` to the displacement
`lft(1) - lft(0)` of the lift. (`E` maps `Lie A` onto `A(ℂ)` with kernel the period lattice, so this
identifies `H₁(A(ℂ), ℚ) ⊗ ℝ` with `Lie A` via the period lattice.) -/
def IsUniformizingIso (E : Lie A → Points A) (ψ : ℝ ⊗[ℚ] bettiOne A ≃ₗ[ℝ] Lie A) : Prop :=
  ∀ (σ : (TopCat.toSSet.obj (space A)) _⦋1⦌)
    (h : (TopCat.toSSet.obj (space A)).δ 0 σ = (TopCat.toSSet.obj (space A)).δ 1 σ)
    (lft : C(StdSimplex ℝ (Fin (⦋1⦌.len + 1)), Lie A)), IsLiftOf A E σ lft →
      ψ (1 ⊗ₜ[ℚ] loopClass A σ h) = lft (.single (Fin.last _)) - lft (.single 0)

/-- Multiplication by `i` on the complex vector space `Lie A`, as an `ℝ`-linear endomorphism. -/
def lieI : Module.End ℝ (Lie A) := (LinearMap.lsmul ℂ (Lie A) Complex.I).restrictScalars ℝ

theorem lieI_apply (v : Lie A) : lieI A v = Complex.I • v := by
  unfold lieI
  rfl

/-- The complex structure on `H₁(A(ℂ), ℚ) ⊗ ℝ` obtained from `i` on `Lie A` through an
`ℝ`-linear identification `ψ`. -/
def transportI (ψ : ℝ ⊗[ℚ] bettiOne A ≃ₗ[ℝ] Lie A) : Module.End ℝ (ℝ ⊗[ℚ] bettiOne A) :=
  ψ.symm.toLinearMap ∘ₗ lieI A ∘ₗ ψ.toLinearMap

theorem transportI_mul_self (ψ : ℝ ⊗[ℚ] bettiOne A ≃ₗ[ℝ] Lie A) :
    transportI A ψ * transportI A ψ = -1 := by
  ext x
  simp [transportI, lieI_apply, ← mul_smul]

/-- **Uniformization data of one object `A`** (Mumford, Milne): the exponential map of the complex
Lie group `A(ℂ)`, the period isomorphism, and the geometric conditions characterizing them.

* `exp` is the exponential map: for each tangent vector `v`, `t ↦ exp (t v)` is a one-parameter
  subgroup with tangent vector `v` (`isExp`), and it is the *unique* one (`exp_unique`);
* `exp` is continuous and surjective, and is a covering map (`exists_lift`: singular `1`-simplices
  lift);
* `period : ℝ ⊗ H₁(A(ℂ), ℚ) ≃ Lie A` sends the class of a loop to the displacement of its lift along
  `exp` (`isPeriod`; the kernel of `exp` is the period lattice) and is the unique such isomorphism
  (`period_unique`).

This is a structure on a *single* object: that every complex abelian variety has such data is a
cited proposition stated in full generality in `External.lean`, not here. -/
structure UniformizationData where
  /-- The exponential map of the complex Lie group `A(ℂ)`. -/
  exp : Lie A → Points A
  /-- `exp` is an exponential map. -/
  isExp : IsExp A exp
  /-- One-parameter subgroups with a given tangent vector are unique. -/
  exp_unique : ∀ (v : Lie A) (φ : ℂ → Points A), IsOneParameter A v φ → φ = fun t => exp (t • v)
  /-- `exp` is continuous for the analytic topology. -/
  continuous_exp : @Continuous (Lie A) (Points A) _ (analyticTopology A) exp
  /-- `exp` is surjective. -/
  surjective_exp : Function.Surjective exp
  /-- `exp` is a covering map: every singular `1`-simplex lifts continuously along `exp`. -/
  exists_lift : ∀ σ : (TopCat.toSSet.obj (space A)) _⦋1⦌,
    ∃ lft : C(StdSimplex ℝ (Fin (⦋1⦌.len + 1)), Lie A), IsLiftOf A exp σ lft
  /-- The period isomorphism `H₁(A(ℂ), ℝ) ≃ Lie A`. -/
  period : ℝ ⊗[ℚ] bettiOne A ≃ₗ[ℝ] Lie A
  /-- The period isomorphism sends loops to displacements of lifts. -/
  isPeriod : IsUniformizingIso A exp period
  /-- It is the unique isomorphism with this property. -/
  period_unique : ∀ ψ : ℝ ⊗[ℚ] bettiOne A ≃ₗ[ℝ] Lie A, IsUniformizingIso A exp ψ → ψ = period
  /-- The analytic space is a finite-dimensional real torus. Milne, Chapter I,
  Proposition 2.1(b), gives the quotient by a full lattice; the proof of
  Theorem 2.3 identifies its topology with a product of circles. -/
  torusTopology : ∃ n : ℕ, Nonempty (space A ≃ₜ (Fin n → Circle))

end Lie

section LieFunctorial

variable {A B : CSch} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

theorem one_comp_points : (1 : Points A) ≫ f = 1 := MonObj.one_comp f

theorem mul_comp_points (p q : Points A) : (p * q) ≫ f = (p ≫ f) * (q ≫ f) :=
  MonObj.mul_comp p q f

theorem idpt_pre {U : B.left.Opens} (hU : secPt (1 : Points B) ∈ U) :
    secPt (1 : Points A) ∈ f.left ⁻¹ᵁ U := by
  have h : secPt ((1 : Points A) ≫ f) = secPt (1 : Points B) :=
    congrArg secPt (one_comp_points f)
  change secPt ((1 : Points A) ≫ f) ∈ U
  rw [h]
  exact hU

/-- **The Lie algebra map of a homomorphism of group schemes**: the Stacks tangent map at the
identity (`tangentMapAt`), followed by the identification `1 ≫ f = 1`. -/
@[expose] def lieMap : Lie A →ₗ[ℂ] Lie B :=
  (TangentAt.cast (one_comp_points f)).toLinearMap ∘ₗ tangentMapAt f 1

theorem tangentEval_lieMap (v : Lie A) (U : B.left.Opens) (hU : secPt (1 : Points B) ∈ U)
    (hU' : secPt (1 : Points A) ∈ f.left ⁻¹ᵁ U) (s : Γ(B.left, U)) :
    tangentEval (lieMap f v) U hU s = tangentEval v (f.left ⁻¹ᵁ U) hU' (f.left.app U s) := by
  have hU'' : secPt ((1 : Points A) ≫ f) ∈ U := hU'
  rw [lieMap, LinearMap.comp_apply, LinearEquiv.coe_coe, tangentEval_cast _ _ U hU'' hU,
    tangentEval_tangentMapAt]

theorem continuous_lieMap : Continuous (lieMap f) := by
  refine continuous_induced_rng.2 (continuous_pi fun U => continuous_pi fun s => ?_)
  have key : (fun v : Lie A => tangentEval (lieMap f v) U.1 U.2 s) =
      fun v => tangentEval v (f.left ⁻¹ᵁ U.1) (idpt_pre f U.2) (f.left.app U.1 s) :=
    funext fun v => tangentEval_lieMap f v _ _ _ _
  change Continuous fun v : Lie A => tangentEval (lieMap f v) U.1 U.2 s
  rw [key]
  have c1 : Continuous fun (v : Lie A) (U : {U : A.left.Opens // secPt (1 : Points A) ∈ U})
      (s : Γ(A.left, U.1)) => tangentEval v U.1 U.2 s := continuous_induced_dom
  exact (continuous_apply (f.left.app U.1 s)).comp
    ((continuous_apply (⟨f.left ⁻¹ᵁ U.1, idpt_pre f U.2⟩ :
      {U : A.left.Opens // secPt (1 : Points A) ∈ U})).comp c1)

theorem lieMap_comp {C : CSch} [GrpObj C] (g : B ⟶ C) [IsMonHom g] (v : Lie A) :
    lieMap (f ≫ g) v = lieMap g (lieMap f v) := by
  refine TangentAt.ext_of_eval fun U hU s => ?_
  rw [tangentEval_lieMap (f ≫ g) v U hU (idpt_pre (f ≫ g) hU) s,
    tangentEval_lieMap g (lieMap f v) U hU (idpt_pre g hU) s,
    tangentEval_lieMap f v (g.left ⁻¹ᵁ U) (idpt_pre g hU) (idpt_pre f (idpt_pre g hU))]
  rfl

theorem lieMap_id (v : Lie A) : lieMap (𝟙 A) v = v := by
  refine TangentAt.ext_of_eval fun U hU s => ?_
  rw [tangentEval_lieMap (𝟙 A) v U hU (idpt_pre (𝟙 A) hU) s]
  rfl

theorem lieMap_congr {g : A ⟶ B} [IsMonHom g] (h : f = g) (v : Lie A) :
    lieMap f v = lieMap g v := by
  subst h
  rfl

/-- One-parameter subgroups are carried to one-parameter subgroups by homomorphisms. -/
theorem IsOneParameter.map {v : Lie A} {φ : ℂ → Points A} (h : IsOneParameter A v φ) :
    IsOneParameter B (lieMap f v) (fun t => φ t ≫ f) where
  map_add s t := by rw [h.map_add]; exact mul_comp_points f _ _
  continuous :=
    @Continuous.comp ℂ (Points A) (Points B) _ (analyticTopology A) (analyticTopology B)
      φ (pointMap f) (continuous_pointMap f) h.continuous
  hasDerivAt U hU s := by
    have h1 := h.hasDerivAt (f.left ⁻¹ᵁ U) (idpt_pre f hU) (f.left.app U s)
    have e : (fun t => ptEval U s (φ t ≫ f)) =
        fun t => ptEval (f.left ⁻¹ᵁ U) (f.left.app U s) (φ t) :=
      funext fun t => ptEval_comp f U s (φ t)
    rw [e, tangentEval_lieMap f v U hU (idpt_pre f hU) s]
    exact h1

/-- **Naturality of the exponential map**: `exp_B (Lie f v) = exp_A v ≫ f`. -/
theorem UniformizationData.exp_lieMap (DA : UniformizationData A) (DB : UniformizationData B)
    (v : Lie A) : DB.exp (lieMap f v) = DA.exp v ≫ f := by
  have h := DB.exp_unique (lieMap f v) _ ((DA.isExp v).map f)
  simpa using (congrFun h 1).symm

end LieFunctorial

section Loops

variable {A B : CSch}

theorem map_face_eq (f : A ⟶ B) (σ : (TopCat.toSSet.obj (space A)) _⦋1⦌)
    (h : (TopCat.toSSet.obj (space A)).δ 0 σ = (TopCat.toSSet.obj (space A)).δ 1 σ) :
    (TopCat.toSSet.obj (space B)).δ 0 ((TopCat.toSSet.map (spaceMap f)).app _ σ) =
      (TopCat.toSSet.obj (space B)).δ 1 ((TopCat.toSSet.map (spaceMap f)).app _ σ) := by
  have := congrArg ((TopCat.toSSet.map (spaceMap f)).app _) h
  simpa [← SSet.δ_naturality_apply] using this

/-- **Naturality of loop classes**: a morphism sends the class of a loop to the class of the image
loop. -/
theorem loopClass_map (f : A ⟶ B) (σ : (TopCat.toSSet.obj (space A)) _⦋1⦌)
    (h : (TopCat.toSSet.obj (space A)).δ 0 σ = (TopCat.toSSet.obj (space A)).δ 1 σ) :
    bettiOneMap f (loopClass A σ h) =
      loopClass B ((TopCat.toSSet.map (spaceMap f)).app _ σ) (map_face_eq f σ h) :=
  congrArg (fun m => m.hom 1) (simplexClassAux_naturality (TopCat.toSSet.map (spaceMap f)) σ h)

private theorem spaceEquiv_map_simplex (f : A ⟶ B) (σ : (TopCat.toSSet.obj (space A)) _⦋1⦌)
    (z : StdSimplex ℝ (Fin (⦋1⦌.len + 1))) :
    spaceEquiv B (TopCat.toSSetObjEquiv (space B) _ ((TopCat.toSSet.map (spaceMap f)).app _ σ) z) =
      pointMap f (spaceEquiv A (TopCat.toSSetObjEquiv (space A) _ σ z)) := rfl

end Loops

section Lie

variable {A : CSch} [GrpObj A]

namespace UniformizationData

/-- The exponential map is independent of the uniformization data. -/
theorem exp_eq (D D' : UniformizationData A) : D.exp = D'.exp := by
  funext v
  have := D.exp_unique v _ (D'.isExp v)
  simpa using (congrFun this 1).symm

/-- The period isomorphism is independent of the uniformization data. -/
theorem period_eq (D D' : UniformizationData A) : D.period = D'.period := by
  refine (D.period_unique D'.period ?_).symm
  rw [D.exp_eq D']
  exact D'.isPeriod

/-- The canonical complex structure on `H₁(A(ℂ), ℝ)`: `i` on `Lie A` transported through the period
isomorphism. -/
@[expose] def J (D : UniformizationData A) : Module.End ℝ (ℝ ⊗[ℚ] bettiOne A) :=
  transportI A D.period

/-- **Independence of the uniformization data.** -/
theorem J_eq (D D' : UniformizationData A) : D.J = D'.J := by
  unfold J
  rw [D.period_eq D']

/-- **The canonical Hodge structure of type `{(-1,0),(0,-1)}` on `H₁(A(ℂ), ℚ)`**, pinned to the
complex geometry of `A`: the complex structure on `H₁(A(ℂ), ℝ)` is transported from `i` on
the Stacks tangent space `Lie A` through the uniformization. -/
@[expose] def canonicalHodge (D : UniformizationData A) : HodgeStructureNegOne (bettiOne A) where
  J := D.J
  J_mul_J := transportI_mul_self A D.period

theorem canonicalHodge_J (D : UniformizationData A) : D.canonicalHodge.J = D.J := rfl

/-- The canonical Hodge structure does not depend on the chosen uniformization data. -/
theorem canonicalHodge_eq (D D' : UniformizationData A) : D.canonicalHodge = D'.canonicalHodge := by
  have h := D.J_eq D'
  cases hD : D.canonicalHodge
  cases hD' : D'.canonicalHodge
  have h1 : D.canonicalHodge.J = D.J := rfl
  have h2 : D'.canonicalHodge.J = D'.J := rfl
  simp only [hD, hD'] at h1 h2
  congr
  rw [h1, h2, h]

end UniformizationData

end Lie

section Functoriality

variable {A B : CSch} [GrpObj A] [GrpObj B]

/-- The classes of closed singular `1`-simplices span `ℝ ⊗ H₁(A(ℂ), ℚ)`. This is proved
(`UniformizationData.loopsSpan`) from the uniqueness of the period isomorphism. -/
def LoopsSpan (A : CSch) : Prop :=
  Submodule.span ℝ (Set.ofPred fun x : ℝ ⊗[ℚ] bettiOne A =>
    ∃ (σ : (TopCat.toSSet.obj (space A)) _⦋1⦌)
      (h : (TopCat.toSSet.obj (space A)).δ 0 σ = (TopCat.toSSet.obj (space A)).δ 1 σ),
      x = 1 ⊗ₜ[ℚ] loopClass A σ h) = ⊤

/-- **Loops span `ℝ ⊗ H₁(A(ℂ), ℚ)`**, proved from the uniqueness of the period isomorphism: were the
span `S` a proper subspace, a linear form `f` vanishing on `S` with `f x₀ ≠ 0` gives the
automorphism `T = id + f(·) w` (`f w = 1`), which is not the identity and fixes `S` pointwise; then
`period ∘ T` is again a uniformizing isomorphism, contradicting `period_unique`. -/
theorem UniformizationData.loopsSpan (D : UniformizationData A) : LoopsSpan A := by
  unfold LoopsSpan
  by_contra hne
  set S := Submodule.span ℝ (Set.ofPred fun x : ℝ ⊗[ℚ] bettiOne A =>
    ∃ (σ : (TopCat.toSSet.obj (space A)) _⦋1⦌)
      (h : (TopCat.toSSet.obj (space A)).δ 0 σ = (TopCat.toSSet.obj (space A)).δ 1 σ),
      x = 1 ⊗ₜ[ℚ] loopClass A σ h) with hS
  obtain ⟨x₀, hx₀⟩ : ∃ x, x ∉ S := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.2 fun x _ => hall x)
  obtain ⟨f, hf, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx₀ inferInstance
  have hfz : ∀ y ∈ S, f y = 0 := fun y hy => by
    have h : f y ∈ S.map f := ⟨y, hy, rfl⟩
    rw [hfS] at h
    simpa using h
  set w : ℝ ⊗[ℚ] bettiOne A := (f x₀)⁻¹ • x₀ with hw
  have hfw : f w = 1 := by
    rw [hw, map_smul, smul_eq_mul, inv_mul_cancel₀ hf]
  have hwx : f x₀ • w = x₀ := by
    rw [hw, smul_smul, mul_inv_cancel₀ hf, one_smul]
  let Te : (ℝ ⊗[ℚ] bettiOne A) ≃ₗ[ℝ] (ℝ ⊗[ℚ] bettiOne A) :=
    { toFun := fun x => x + f x • w
      map_add' := fun x y => by
        simp only [map_add, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        module
      invFun := fun x => x - (1 / 2 * f x) • w
      left_inv := fun x => by
        simp only [map_add, map_smul, smul_eq_mul, hfw]
        module
      right_inv := fun x => by
        simp only [map_sub, map_smul, smul_eq_mul, hfw]
        module }
  have hTS : ∀ y ∈ S, Te y = y := fun y hy => by
    change y + f y • w = y
    rw [hfz y hy, zero_smul, add_zero]
  have huni : IsUniformizingIso A D.exp (Te.trans D.period) := by
    intro σ h lft hlft
    have hmem : (1 : ℝ) ⊗ₜ[ℚ] loopClass A σ h ∈ S :=
      Submodule.subset_span ⟨σ, h, rfl⟩
    rw [LinearEquiv.trans_apply, hTS _ hmem]
    exact D.isPeriod σ h lft hlft
  have hEq := D.period_unique _ huni
  have hx : D.period (Te x₀) = D.period x₀ := by
    have := congrArg (fun ψ => ψ x₀) hEq
    simpa using this
  have hT : Te x₀ = x₀ := D.period.injective hx
  have h3 : Te x₀ = x₀ + x₀ := by
    change x₀ + f x₀ • w = x₀ + x₀
    rw [hwx]
  have h4 : x₀ = 0 := by
    have : x₀ + x₀ = x₀ := h3.symm.trans hT
    simpa using this
  exact hx₀ (h4 ▸ S.zero_mem)

/-- The map `ℝ ⊗ H₁(A) → ℝ ⊗ H₁(B)` induced by a morphism. -/
@[expose] def bettiMapR (f : A ⟶ B) : ℝ ⊗[ℚ] bettiOne A →ₗ[ℝ] ℝ ⊗[ℚ] bettiOne B :=
  TensorProduct.AlgebraTensorModule.map LinearMap.id (bettiOneMap f)

/-- **Naturality of the period isomorphism along a morphism** of group schemes: no hypothesis (loops
span homology by `UniformizationData.loopsSpan`). -/
theorem UniformizationData.period_map (f : A ⟶ B) [IsMonHom f] (DA : UniformizationData A)
    (DB : UniformizationData B) (x : ℝ ⊗[ℚ] bettiOne A) :
    DB.period (bettiMapR f x) = lieMap f (DA.period x) := by
  have key : DB.period.toLinearMap ∘ₗ bettiMapR f =
      ((lieMap f).restrictScalars ℝ) ∘ₗ DA.period.toLinearMap := by
    have hspan := DA.loopsSpan
    unfold LoopsSpan at hspan
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨σ, h, rfl⟩
    obtain ⟨lft, hlft⟩ := DA.exists_lift σ
    have hA := DA.isPeriod σ h lft hlft
    have hB := DB.isPeriod ((TopCat.toSSet.map (spaceMap f)).app _ σ) (map_face_eq f σ h)
      ((⟨lieMap f, continuous_lieMap f⟩ : C(Lie A, Lie B)).comp lft) (fun z => by
        change DB.exp (lieMap f (lft z)) = _
        rw [DA.exp_lieMap f DB (lft z), hlft z]
        rfl)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, bettiMapR,
      TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    rw [loopClass_map, hB, hA]
    simp
  exact congrArg (fun m => m x) key

theorem UniformizationData.period_J (D : UniformizationData A) (z : ℝ ⊗[ℚ] bettiOne A) :
    D.period (D.J z) = lieI A (D.period z) := by
  simp [UniformizationData.J, transportI]

/-- **The canonical complex structure is natural along every homomorphism of group schemes**:
`H₁(f)` is a morphism of the canonical Hodge structures, `J_B ∘ H₁(f) = H₁(f) ∘ J_A`. -/
theorem UniformizationData.J_map (f : A ⟶ B) [IsMonHom f] (DA : UniformizationData A)
    (DB : UniformizationData B) (x : ℝ ⊗[ℚ] bettiOne A) :
    DB.J (bettiMapR f x) = bettiMapR f (DA.J x) := by
  apply DB.period.injective
  rw [DB.period_J, DA.period_map f DB, DA.period_map f DB, DA.period_J, lieI_apply, lieI_apply]
  exact (map_smul (lieMap f) Complex.I (DA.period x)).symm

variable (e : A ≅ B) [IsMonHom e.hom]

theorem lieMap_hom_inv (v : Lie B) : lieMap e.hom (lieMap e.inv v) = v :=
  (lieMap_comp e.inv e.hom v).symm.trans
    ((lieMap_congr (e.inv ≫ e.hom) e.inv_hom_id v).trans (lieMap_id v))

theorem lieMap_inv_hom (v : Lie A) : lieMap e.inv (lieMap e.hom v) = v :=
  (lieMap_comp e.hom e.inv v).symm.trans
    ((lieMap_congr (e.hom ≫ e.inv) e.hom_inv_id v).trans (lieMap_id v))

/-- **An isomorphism of group schemes induces an isomorphism of Lie algebras.** -/
def lieEquiv : Lie A ≃ₗ[ℂ] Lie B :=
  LinearEquiv.ofLinearMap (lieMap e.hom) (lieMap e.inv)
    (LinearMap.ext (lieMap_hom_inv e)) (LinearMap.ext (lieMap_inv_hom e))

/-- **An isomorphism induces an isomorphism of Betti spaces** `ℝ ⊗ H₁(A) ≃ ℝ ⊗ H₁(B)`. -/
@[expose] def bettiR : ℝ ⊗[ℚ] bettiOne A ≃ₗ[ℝ] ℝ ⊗[ℚ] bettiOne B :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℝ ℝ) (bettiLinearEquiv 1 e)

omit [GrpObj A] [GrpObj B] [IsMonHom e.hom] in
theorem bettiR_symm_tmul (y : bettiOne B) :
    (bettiR e).symm (1 ⊗ₜ[ℚ] y) = 1 ⊗ₜ[ℚ] bettiOneMap e.inv y := by
  apply (bettiR e).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [bettiR, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    bettiLinearEquiv_apply]
  rw [show (bettiMap 1 e.hom).hom (bettiOneMap e.inv y) = bettiOneMap e.hom (bettiOneMap e.inv y)
    from rfl, ← bettiOneMap_comp, e.inv_hom_id, bettiOneMap_id]

/-- **Naturality of the period isomorphism along an isomorphism of group schemes** (no hypothesis:
the characterization of the period isomorphism is transported). -/
theorem UniformizationData.period_iso (DA : UniformizationData A) (DB : UniformizationData B)
    (x : ℝ ⊗[ℚ] bettiOne A) : DB.period (bettiR e x) = lieEquiv e (DA.period x) := by
  have key : (bettiR e).symm.trans (DA.period.trans ((lieEquiv e).restrictScalars ℝ)) =
      DB.period := by
    apply DB.period_unique
    intro σ h lft hlft
    have hA := DA.isPeriod ((TopCat.toSSet.map (spaceMap e.inv)).app _ σ) (map_face_eq e.inv σ h)
      ((⟨lieMap e.inv, continuous_lieMap e.inv⟩ : C(Lie B, Lie A)).comp lft) (fun z => by
        change DA.exp (lieMap e.inv (lft z)) = _
        rw [DB.exp_lieMap e.inv DA (lft z), hlft z]
        rfl)
    simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
    rw [bettiR_symm_tmul, loopClass_map, hA]
    have hh : ∀ w, lieEquiv e (lieMap e.inv w) = w := lieMap_hom_inv e
    change lieEquiv e _ = _
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, map_sub, hh]
  have := congrArg (fun ψ => ψ (bettiR e x)) key
  simpa using this.symm

/-- **The canonical complex structure is natural along isomorphisms of group schemes**:
`J_B ∘ H₁(e) = H₁(e) ∘ J_A`. -/
theorem UniformizationData.J_iso (DA : UniformizationData A) (DB : UniformizationData B)
    (x : ℝ ⊗[ℚ] bettiOne A) : DB.J (bettiR e x) = bettiR e (DA.J x) := by
  apply DB.period.injective
  rw [DB.period_J, DA.period_iso e DB, DA.period_iso e DB, DA.period_J]
  rw [lieI_apply, lieI_apply]
  exact (map_smul (lieEquiv e) Complex.I (DA.period x)).symm

end Functoriality

section Product

open CartesianMonoidalCategory MonoidalCategory

variable (A B : CSch) [GrpObj A] [GrpObj B]

/-- **The Lie algebra of a product is the product of the Lie algebras**: the pair of Lie algebra
maps of the two projections is bijective. This is the Stacks product decomposition of tangent spaces
(`AlgebraicGeometry.tangentSpaceProductEquiv`, tag 0BEB) at the identity point. -/
theorem lieProd_bijective :
    Function.Bijective (fun v : Lie (A ⊗ B) => (lieMap (fst A B) v, lieMap (snd A B) v)) := by
  let σ : Points (A ⊗ B) := 1
  let z : ↑(pullback A.hom B.hom) := secPt σ
  have h1 : IsIso (A.hom.residueFieldMap (pullback.fst A.hom B.hom z)) :=
    isIso_residueFieldMap (Over.homMk A.hom (Category.comp_id _) : A ⟶ Over.mk (𝟙 _))
      (σ ≫ fst A B)
  have h2 : IsIso (B.hom.residueFieldMap (pullback.snd A.hom B.hom z)) :=
    isIso_residueFieldMap (Over.homMk B.hom (Category.comp_id _) : B ⟶ Over.mk (𝟙 _))
      (σ ≫ snd A B)
  let E := tangentSpaceProductEquiv A.hom B.hom z
  have hbij : Function.Bijective E.toLinearEquiv := E.toLinearEquiv.bijective
  have hb : Function.Bijective (fun w : DottedTangentArrow A.hom (pullback.fst A.hom B.hom z) ×
      DottedTangentArrow B.hom (pullback.snd A.hom B.hom z) =>
      (TangentAt.cast (one_comp_points (fst A B)) w.1,
       TangentAt.cast (one_comp_points (snd A B)) w.2)) :=
    Function.Bijective.prodMap (TangentAt.cast (one_comp_points (fst A B))).bijective
      (TangentAt.cast (one_comp_points (snd A B))).bijective
  have key : (fun v : Lie (A ⊗ B) => (lieMap (fst A B) v, lieMap (snd A B) v)) =
      (fun w : DottedTangentArrow A.hom (pullback.fst A.hom B.hom z) ×
        DottedTangentArrow B.hom (pullback.snd A.hom B.hom z) =>
        (TangentAt.cast (one_comp_points (fst A B)) w.1,
         TangentAt.cast (one_comp_points (snd A B)) w.2)) ∘ E.toLinearEquiv := by
    funext v
    have hv := E.toLinearEquiv_apply v
    refine Prod.ext ?_ ?_
    · exact congrArg (TangentAt.cast (one_comp_points (fst A B)))
        ((tangentMapAt_apply (fst A B) 1 v).trans (congrArg Prod.fst hv).symm)
    · exact congrArg (TangentAt.cast (one_comp_points (snd A B)))
        ((tangentMapAt_apply (snd A B) 1 v).trans (congrArg Prod.snd hv).symm)
  rw [key]
  exact hb.comp hbij

/-- The map `H₁((A ⊗ B)(ℂ), ℚ) → H₁(A(ℂ), ℚ) × H₁(B(ℂ), ℚ)` induced by the two projections. -/
@[expose] def bettiProd : bettiOne (A ⊗ B) →ₗ[ℚ] bettiOne A × bettiOne B :=
  LinearMap.prod (bettiOneMap (fst A B)) (bettiOneMap (snd A B))

/-- The real extension of `bettiProd`. -/
@[expose] def bettiProdR :
    ℝ ⊗[ℚ] bettiOne (A ⊗ B) →ₗ[ℝ] (ℝ ⊗[ℚ] bettiOne A) × (ℝ ⊗[ℚ] bettiOne B) :=
  LinearMap.prod (bettiMapR (fst A B)) (bettiMapR (snd A B))

/-- **Künneth for `H₁` of a product of abelian varieties, over `ℝ`**, proved from the uniformization
data and the Stacks tangent product decomposition (not from a Künneth theorem for singular
homology): the period isomorphisms are natural along the projections, and
`Lie (A ⊗ B) ≅ Lie A × Lie B`. -/
theorem bettiProdR_bijective (DA : UniformizationData A) (DB : UniformizationData B)
    (DP : UniformizationData (A ⊗ B)) : Function.Bijective (bettiProdR A B) := by
  let ψ : ((ℝ ⊗[ℚ] bettiOne A) × (ℝ ⊗[ℚ] bettiOne B)) ≃ₗ[ℝ] (Lie A × Lie B) :=
    DA.period.prodCongr DB.period
  have hcomp : ∀ x, ψ (bettiProdR A B x) =
      (lieMap (fst A B) (DP.period x), lieMap (snd A B) (DP.period x)) := fun x =>
    Prod.ext (DP.period_map (fst A B) DA x) (DP.period_map (snd A B) DB x)
  have hfun : ⇑(bettiProdR A B) = ⇑ψ.symm ∘
      (fun v : Lie (A ⊗ B) => (lieMap (fst A B) v, lieMap (snd A B) v)) ∘ ⇑DP.period := by
    funext x
    exact ψ.eq_symm_apply.2 (hcomp x)
  rw [hfun]
  exact ψ.symm.bijective.comp ((lieProd_bijective A B).comp DP.period.bijective)

/-- **Künneth for `H₁` of a product of abelian varieties, over `ℚ`.** -/
theorem bettiProd_bijective (DA : UniformizationData A) (DB : UniformizationData B)
    (DP : UniformizationData (A ⊗ B)) : Function.Bijective (bettiProd A B) := by
  have hfun : ∀ x, TensorProduct.prodRight ℚ ℝ ℝ (bettiOne A) (bettiOne B)
      ((bettiProd A B).lTensor ℝ x) = bettiProdR A B x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r y => simp [bettiProd, bettiProdR, bettiMapR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hR : Function.Bijective ((bettiProd A B).lTensor ℝ) := by
    have h : ⇑((bettiProd A B).lTensor ℝ) =
        ⇑(TensorProduct.prodRight ℚ ℝ ℝ (bettiOne A) (bettiOne B)).symm ∘ ⇑(bettiProdR A B) := by
      funext x
      exact ((TensorProduct.prodRight ℚ ℝ ℝ (bettiOne A) (bettiOne B)).eq_symm_apply).2 (hfun x)
    rw [h]
    exact (TensorProduct.prodRight ℚ ℝ ℝ (bettiOne A) (bettiOne B)).symm.bijective.comp
      (bettiProdR_bijective A B DA DB DP)
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective ℚ ℝ (bettiProd A B)).1 hR

/-- **The canonical complex structure of a product is the product of the canonical complex
structures**: `H₁` of the projections is a morphism of canonical Hodge structures. -/
theorem bettiProdR_J (DA : UniformizationData A) (DB : UniformizationData B)
    (DP : UniformizationData (A ⊗ B)) (x : ℝ ⊗[ℚ] bettiOne (A ⊗ B)) :
    bettiProdR A B (DP.J x) = (DA.J (bettiProdR A B x).1, DB.J (bettiProdR A B x).2) :=
  Prod.ext (DP.J_map (fst A B) DA x).symm (DP.J_map (snd A B) DB x).symm

end Product

section Polarization

open HodgeStructureNegOne

variable {W V' : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup V'] [Module ℚ V']

/-- The real extension of a `ℚ`-linear isomorphism, as an `ℝ`-linear isomorphism. -/
abbrev realEquiv (Φ : W ≃ₗ[ℚ] V') : ℝ ⊗[ℚ] W ≃ₗ[ℝ] ℝ ⊗[ℚ] V' :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℝ ℝ) Φ

/-- The real extension of the pullback of a bilinear form is the pullback of its real extension. -/
theorem baseChange_compl₁₂_realEquiv (B : LinearMap.BilinForm ℚ V') (Φ : W ≃ₗ[ℚ] V')
    (x y : ℝ ⊗[ℚ] W) :
    LinearMap.BilinForm.baseChange ℝ (B.compl₁₂ Φ.toLinearMap Φ.toLinearMap) x y =
      LinearMap.BilinForm.baseChange ℝ B (realEquiv Φ x) (realEquiv Φ y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a w =>
    induction y using TensorProduct.inductionOn with
    | tmul b w' => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-- **Transport of a polarization along an isomorphism of Hodge structures**: if `Φ : W ≃ V'` is a
`ℚ`-linear isomorphism whose real extension intertwines the complex structures, a polarization of
`V'` pulls back to a polarization of `W`. -/
@[expose] def _root_.ArithmeticOfJacobiPolynomials.HodgeStructureNegOne.Polarization.comap
    {HW : HodgeStructureNegOne W} {H' : HodgeStructureNegOne V'} (P : H'.Polarization)
    (Φ : W ≃ₗ[ℚ] V') (hJ : ∀ x, realEquiv Φ (HW.J x) = H'.J (realEquiv Φ x)) :
    HW.Polarization where
  form := P.form.compl₁₂ Φ.toLinearMap Φ.toLinearMap
  form_self x := P.form_self _
  baseChange_J x y := by
    rw [baseChange_compl₁₂_realEquiv, baseChange_compl₁₂_realEquiv, hJ, hJ]
    exact P.baseChange_J _ _
  pos x hx := by
    rw [baseChange_compl₁₂_realEquiv, hJ]
    exact P.pos _ fun h => hx ((realEquiv Φ).injective (by rw [h, map_zero]))

variable {A B : CSch} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]

/-- **Riemann forms are transported along isomorphisms of abelian varieties**: a polarization of the
canonical Hodge structure of `B` pulls back along `H₁(e)` to one of `A` (`J_iso` supplies the
intertwining). -/
@[expose] def UniformizationData.riemannFormOfIso (DA : UniformizationData A)
    (DB : UniformizationData B) (P : DB.canonicalHodge.Polarization) :
    DA.canonicalHodge.Polarization :=
  P.comap (bettiLinearEquiv 1 e) fun x => (DA.J_iso e DB x).symm

end Polarization

section Power

open CartesianMonoidalCategory MonoidalCategory ArithmeticOfJacobiPolynomials.GroupScheme

variable (A : CSch) [GrpObj A]

/-- The `i`-th projection `A^(h+1) ⟶ A` of the power `powObj ℂ A (h + 1)`. -/
@[expose] noncomputable def powProj (h : ℕ) : Fin (h + 1) → (powObj ℂ A (h + 1) ⟶ A) :=
  Nat.rec (motive := fun h => Fin (h + 1) → (powObj ℂ A (h + 1) ⟶ A))
    (fun _ => fst A (powObj ℂ A 0))
    (fun h ih i => Fin.cases (fst A (powObj ℂ A (h + 1)))
      (fun j => snd A (powObj ℂ A (h + 1)) ≫ ih j) i) h

omit [GrpObj A] in
theorem powProj_zero (i : Fin 1) : powProj A 0 i = fst A (powObj ℂ A 0) := rfl

omit [GrpObj A] in
theorem powProj_succ_zero (h : ℕ) :
    powProj A (h + 1) 0 = fst A (powObj ℂ A (h + 1)) := rfl

omit [GrpObj A] in
theorem powProj_succ_succ (h : ℕ) (j : Fin (h + 1)) :
    powProj A (h + 1) j.succ = snd A (powObj ℂ A (h + 1)) ≫ powProj A h j := rfl

instance isMonHom_powProj (h : ℕ) (i : Fin (h + 1)) : IsMonHom (powProj A h i) := by
  induction h with
  | zero => exact inferInstanceAs (IsMonHom (fst A (powObj ℂ A 0)))
  | succ h ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact inferInstanceAs (IsMonHom (fst A (powObj ℂ A (h + 1))))
    · rw [powProj_succ_succ]
      have := ih j
      exact inferInstanceAs (IsMonHom (snd A (powObj ℂ A (h + 1)) ≫ powProj A h j))

theorem bettiOneMap_bijective_of_isIso {X Y : CSch} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective (bettiOneMap f) := by
  have h := (bettiLinearEquiv 1 (asIso f)).bijective
  have e : ⇑(bettiLinearEquiv 1 (asIso f)) = ⇑(bettiOneMap f) :=
    funext fun x => bettiLinearEquiv_apply 1 (asIso f) x
  rwa [e] at h

/-- The projections `A^(h+1) ⟶ A` induce `H₁(A^(h+1)) → H₁(A)^(h+1)`. -/
@[expose] noncomputable def bettiPow (h : ℕ) :
    bettiOne (powObj ℂ A (h + 1)) →ₗ[ℚ] (Fin (h + 1) → bettiOne A) :=
  LinearMap.pi fun i => bettiOneMap (powProj A h i)

/-- **`H₁(A^(h+1)) ≅ H₁(A)^(h+1)` (Künneth for powers)**, proved by induction from the product
case `bettiProd_bijective` from the uniformization data of the powers. -/
theorem bettiPow_bijective (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (powObj ℂ A (h + 1))) (h : ℕ) :
    Function.Bijective (bettiPow A h) := by
  induction h with
  | zero =>
    have hi : IsIso (fst A (powObj ℂ A 0)) := by
      have h0 : IsIso (fst A (𝟙_ (Over (Spec (CommRingCat.of ℂ))))) := by
        rw [← rightUnitor_hom]
        infer_instance
      exact h0
    have hb := bettiOneMap_bijective_of_isIso (fst A (powObj ℂ A 0))
    have e : ⇑(bettiPow A 0) = ⇑(Equiv.funUnique (Fin 1) (bettiOne A)).symm ∘
        ⇑(bettiOneMap (fst A (powObj ℂ A 0))) := rfl
    rw [e]
    exact (Equiv.funUnique (Fin 1) (bettiOne A)).symm.bijective.comp hb
  | succ h hrec =>
    have hP := bettiProd_bijective A (powObj ℂ A (h + 1)) DA (D h) (D (h + 1))
    have e : ⇑(bettiPow A (h + 1)) = ⇑(Fin.consEquiv (fun _ : Fin (h + 2) => bettiOne A)) ∘
        Prod.map id (bettiPow A h) ∘ ⇑(bettiProd A (powObj ℂ A (h + 1))) := by
      funext x i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change bettiOneMap (powProj A (h + 1) j.succ) x =
          (Fin.cons (bettiOneMap (fst A (powObj ℂ A (h + 1))) x)
            (bettiPow A h (bettiOneMap (snd A (powObj ℂ A (h + 1))) x)) :
              Fin (h + 2) → bettiOne A) j.succ
        rw [Fin.cons_succ, powProj_succ_succ]
        exact bettiOneMap_comp (snd A (powObj ℂ A (h + 1))) (powProj A h j) x
    rw [e]
    exact (Fin.consEquiv (fun _ : Fin (h + 2) => bettiOne A)).bijective.comp
      ((Function.bijective_id.prodMap hrec).comp hP)

/-- `H₁(A^(h+1)) ≃ H₁(A)^(h+1)`. -/
@[expose] noncomputable def bettiPowEquiv (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (powObj ℂ A (h + 1))) (h : ℕ) :
    bettiOne (powObj ℂ A (h + 1)) ≃ₗ[ℚ] (Fin (h + 1) → bettiOne A) :=
  LinearEquiv.ofBijective (bettiPow A h) (bettiPow_bijective A DA D h)

theorem realPiEquiv_realEquiv_bettiPowEquiv (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (powObj ℂ A (h + 1))) (h : ℕ)
    (y : ℝ ⊗[ℚ] bettiOne (powObj ℂ A (h + 1))) (i : Fin (h + 1)) :
    ArithmeticOfJacobiPolynomials.HodgeStructureNegOne.realPiEquiv (bettiOne A) (Fin (h + 1))
      (realEquiv (bettiPowEquiv A DA D h) y) i = bettiMapR (powProj A h i) y := by
  induction y using TensorProduct.inductionOn with
  | tmul a w =>
    simp only [realEquiv, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      ArithmeticOfJacobiPolynomials.HodgeStructureNegOne.realPiEquiv_tmul, bettiMapR,
      TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realEquiv_bettiPowEquiv_J (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (powObj ℂ A (h + 1))) (h : ℕ)
    (x : ℝ ⊗[ℚ] bettiOne (powObj ℂ A (h + 1))) :
    realEquiv (bettiPowEquiv A DA D h) ((D h).canonicalHodge.J x) =
      (DA.canonicalHodge.pi (Fin (h + 1))).J (realEquiv (bettiPowEquiv A DA D h) x) := by
  apply (ArithmeticOfJacobiPolynomials.HodgeStructureNegOne.realPiEquiv (bettiOne A) (Fin (h +
    1))).injective
  rw [ArithmeticOfJacobiPolynomials.HodgeStructureNegOne.realPiEquiv_pi_J]
  funext i
  rw [realPiEquiv_realEquiv_bettiPowEquiv, realPiEquiv_realEquiv_bettiPowEquiv]
  exact ((D h).J_map (powProj A h i) DA x).symm

/-- **A polarization of `A` gives the orthogonal-sum polarization of the canonical Hodge structure
of `A^(h+1)`.** -/
noncomputable def UniformizationData.riemannFormPow (DA : UniformizationData A)
    (D : ∀ h, UniformizationData (powObj ℂ A (h + 1))) (h : ℕ)
    (P : DA.canonicalHodge.Polarization) : (D h).canonicalHodge.Polarization :=
  (P.pow (h + 1)).comap (bettiPowEquiv A DA D h) (realEquiv_bettiPowEquiv_J A DA D h)

end Power

end ArithmeticOfJacobiPolynomials.AbelianBettiHodge
