/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianVariety
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZeroSubfunctor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Normalized

/-!
# The Jacobian of a curve, characterized by its universal property

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism of dimension at most one (a curve, in
the cases of interest smooth projective and geometrically irreducible), living in a big fppf site
`B` (the formalism of the Stacks library). The **relative Picard functor** `Pic_{X/k}` is the fppf
sheafification of `T ↦ Pic(X ×_k T)` (`Stacks.PicardFunctor.picardFunctor`, [Stacks, Tag 0B9L]).

**`Pic⁰_{X/k}` is cut out at geometric points.** A section `ξ ∈ Pic_{X/k}(T)` lies in
`Pic⁰_{X/k}(T)` when for every geometric point `Spec Ω ⟶ T` of the site (`Ω` an algebraically
closed field) the pullback `ξ_Ω ∈ Pic_{X/k}(Ω)` is the class of a degree-zero invertible module on
`X_Ω` (`ArithmeticOfJacobiPolynomials.Jacobian.IsGeomFibrewiseDegreeZero`).
For a smooth projective geometrically integral curve, `X_Ω` has a rational point, so
`Pic(X_Ω) ⟶ Pic_{X/k}(Ω)` is bijective ([Stacks, Tag 0B9N]). When the Picard sheaf is represented
by a scheme `P`, this condition says that the morphism `T ⟶ P` lands in the open and closed
component `P⁰`. The spectrum of an algebraic closure of every residue field of `T` lies in the
site, so the geometric points in the condition detect membership in `P⁰`.

The Stacks subfunctor `Stacks.PicardFunctor.degreeZeroSubfunctor` tests at the residue fields
`κ(t)`. It is contained in the geometric-point subfunctor, and the two agree over an algebraically
closed ground field for smooth projective curves (see `Geometry.Jacobian.GeometricFibre`).

* `ArithmeticOfJacobiPolynomials.Jacobian.degreeZeroAddSubgroup`: the subgroup
  `Pic⁰_{X/k}(T) ≤ Pic_{X/k}(T)` of geometrically degree-zero sections;
* `ArithmeticOfJacobiPolynomials.Jacobian.degreeZeroGrpFunctor`: the presheaf of groups
  `T ↦ Pic⁰_{X/k}(T)`;
* `ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf B hX hk f hdim G`: the group scheme `G` over
  `k` **represents `Pic⁰_{X/k}`** (a natural isomorphism of groups `Hom_k(T, G) ≃* Pic⁰_{X/k}(T)`
  for every `T` of the site over `k`) **and is an abelian variety**
  (`AlgebraicGeometry.IsAbelianVariety`, [Stacks, Tag 03RO]). The existence of `G` over
  algebraically closed fields is the theorem
  `ArithmeticOfJacobiPolynomials.Jacobian.exists_isJacobianOf_of_isAlgClosed` (from [Stacks, Tags
  0B9Z, 0BA0]), and over a general field it is the hypothesis
  `ArithmeticOfJacobiPolynomials.Jacobian.JacobianExists` ([MilneJV, Theorem 1.1, Remark 1.7,
  Proposition 1.9]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Jacobian

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

/-- The restriction maps of the Picard functor `Pic_{X/k}`, as additive homomorphisms. -/
def picardRestrictAddHom {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T) :
    (picardFunctor B hX hk f).obj (op T) →+ (picardFunctor B hX hk f).obj (op T') where
  toFun := (picardFunctor B hX hk f).map g.op
  map_zero' := picardFunctor_map_zero B hX hk f g
  map_add' := picardFunctor_map_add B hX hk f g

/-- **A geometric test scheme**: `Spec Ω` for a field `Ω` (algebraically closed in the uses
below), with a structure morphism `s : Spec Ω ⟶ Spec k`, as an object of the site over `k`. -/
abbrev geomTest (Ω : Type u) [Field Ω] (hΩ : B.Contains (Spec (.of Ω)))
    (s : Spec (.of Ω) ⟶ Spec (.of k)) : BigFppfOver B (Spec (.of k)) hk :=
  siteObject B (Spec (.of k)) hk hΩ s

section DegreeZero

variable [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1)

/-- **The residue-field degree-zero sections** (the Stacks subfunctor
`Stacks.PicardFunctor.degreeZeroSubfunctor`, as a subgroup): the sections all of whose fibres
`ξ_t ∈ Pic_{X/k}(κ(t))` are classes of degree-zero invertible modules on `X_{κ(t)}`. This is
**not** `Pic⁰_{X/k}` over a general field (see the module docstring); it is used only on geometric
test schemes, where it is correct. -/
def fibrewiseDegreeZeroAddSubgroup (T : BigFppfOver B (Spec (.of k)) hk) :
    AddSubgroup ((picardFunctor B hX hk f).obj (op T)) where
  carrier := {ξ | IsFibrewiseDegreeZero B hX hk f hdim T ξ}
  zero_mem' t :=
    ⟨0, zero_mem _, by
      rw [toPicardFunctor_app_zero]
      exact (picardFunctor_map_zero B hX hk f (residueTestι B hk T t)).symm⟩
  add_mem' {a b} ha hb t := by
    obtain ⟨L, hL, hLa⟩ := ha t
    obtain ⟨L', hL', hLb⟩ := hb t
    refine ⟨L + L', add_mem hL hL', ?_⟩
    rw [toPicardFunctor_app_add, hLa, hLb, picardFunctor_map_add]
  neg_mem' {a} ha t := by
    obtain ⟨L, hL, hLa⟩ := ha t
    refine ⟨-L, neg_mem hL, ?_⟩
    have h1 := map_neg (toPicardFunctorHom B hX hk f (residueTest B hk T t)) L
    have h2 := map_neg (picardRestrictAddHom B hX hk f (residueTestι B hk T t)) a
    refine h1.trans ?_
    refine Eq.trans (congrArg Neg.neg hLa) ?_
    exact h2.symm

/-- Membership in the residue-field subgroup is the Stacks fibrewise condition. -/
theorem mem_fibrewiseDegreeZeroAddSubgroup {T : BigFppfOver B (Spec (.of k)) hk}
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    ξ ∈ fibrewiseDegreeZeroAddSubgroup B hX hk f hdim T ↔
      IsFibrewiseDegreeZero B hX hk f hdim T ξ :=
  Iff.rfl

/-- **The geometric-fibre degree-zero condition.** A section `ξ ∈ Pic_{X/k}(T)` has degree zero
on every geometric fibre when, for every algebraically closed field `Ω` with `Spec Ω` in the site
and every `k`-morphism `e : Spec Ω ⟶ T`, the pullback `e^*ξ` is the class of a degree-zero
invertible module on `X_Ω` (the Stacks condition `Stacks.PicardFunctor.IsFibrewiseDegreeZero` at
the one-point test scheme `Spec Ω`). -/
def IsGeomFibrewiseDegreeZero (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (hΩ : B.Contains (Spec (.of Ω)))
    (s : Spec (.of Ω) ⟶ Spec (.of k)) (e : geomTest B hk Ω hΩ s ⟶ T),
    IsFibrewiseDegreeZero B hX hk f hdim (geomTest B hk Ω hΩ s)
      ((picardFunctor B hX hk f).map e.op ξ)

/-- **The residue-field condition implies the geometric one**, over any field: the Stacks
subfunctor is stable under pullback to `Spec Ω`. -/
theorem isGeomFibrewiseDegreeZero_of_isFibrewiseDegreeZero {T : BigFppfOver B (Spec (.of k)) hk}
    {ξ : (picardFunctor B hX hk f).obj (op T)} (h : IsFibrewiseDegreeZero B hX hk f hdim T ξ) :
    IsGeomFibrewiseDegreeZero B hX hk f hdim T ξ := by
  intro Ω _ _ hΩ s e
  exact isFibrewiseDegreeZero_map B hX hk f hdim e h

/-- **The geometric-fibre condition is stable under restriction**: a geometric point of `T'`
followed by `g : T' ⟶ T` is a geometric point of `T`. -/
theorem isGeomFibrewiseDegreeZero_map {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    {ξ : (picardFunctor B hX hk f).obj (op T)} (hξ : IsGeomFibrewiseDegreeZero B hX hk f hdim T ξ) :
    IsGeomFibrewiseDegreeZero B hX hk f hdim T' ((picardFunctor B hX hk f).map g.op ξ) := by
  intro Ω _ _ hΩ s e
  have h := hξ Ω hΩ s (e ≫ g)
  rwa [op_comp, Functor.map_comp_apply] at h

/-- **`Pic⁰_{X/k}` as a subfunctor of the Picard sheaf**: the sections of degree zero on every
geometric fibre. -/
def geomDegreeZeroSubfunctor : Subfunctor (picardFunctor B hX hk f) where
  obj T := {ξ | IsGeomFibrewiseDegreeZero B hX hk f hdim T.unop ξ}
  map g _ hξ := isGeomFibrewiseDegreeZero_map B hX hk f hdim g.unop hξ

/-- **`Pic⁰_{X/k}(T)` as a subgroup of `Pic_{X/k}(T)`**: the sections of degree zero on every
geometric fibre (`ArithmeticOfJacobiPolynomials.Jacobian.IsGeomFibrewiseDegreeZero`). -/
def degreeZeroAddSubgroup (T : BigFppfOver B (Spec (.of k)) hk) :
    AddSubgroup ((picardFunctor B hX hk f).obj (op T)) where
  carrier := {ξ | IsGeomFibrewiseDegreeZero B hX hk f hdim T ξ}
  zero_mem' := by
    change IsGeomFibrewiseDegreeZero B hX hk f hdim T 0
    intro Ω _ _ hΩ s e
    rw [picardFunctor_map_zero B hX hk f e]
    exact (fibrewiseDegreeZeroAddSubgroup B hX hk f hdim _).zero_mem
  add_mem' {a b} ha hb := by
    have ha' : IsGeomFibrewiseDegreeZero B hX hk f hdim T a := ha
    have hb' : IsGeomFibrewiseDegreeZero B hX hk f hdim T b := hb
    change IsGeomFibrewiseDegreeZero B hX hk f hdim T (a + b)
    intro Ω _ _ hΩ s e
    rw [picardFunctor_map_add B hX hk f e]
    exact (fibrewiseDegreeZeroAddSubgroup B hX hk f hdim _).add_mem (ha' Ω hΩ s e)
      (hb' Ω hΩ s e)
  neg_mem' {a} ha := by
    have ha' : IsGeomFibrewiseDegreeZero B hX hk f hdim T a := ha
    change IsGeomFibrewiseDegreeZero B hX hk f hdim T (-a)
    intro Ω _ _ hΩ s e
    have h := map_neg (picardRestrictAddHom B hX hk f e) a
    change picardRestrictAddHom B hX hk f e (-a) ∈ fibrewiseDegreeZeroAddSubgroup B hX hk f hdim _
    rw [h]
    exact (fibrewiseDegreeZeroAddSubgroup B hX hk f hdim _).neg_mem (ha' Ω hΩ s e)

/-- A section lies in `Pic⁰_{X/k}(T)` iff it has degree zero on every geometric fibre. -/
theorem mem_degreeZeroAddSubgroup {T : BigFppfOver B (Spec (.of k)) hk}
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    ξ ∈ degreeZeroAddSubgroup B hX hk f hdim T ↔ IsGeomFibrewiseDegreeZero B hX hk f hdim T ξ :=
  Iff.rfl

/-- The subgroup `Pic⁰_{X/k}(T)` is the value of the subfunctor
`ArithmeticOfJacobiPolynomials.Jacobian.geomDegreeZeroSubfunctor` at `T`. -/
theorem mem_degreeZeroAddSubgroup_iff_mem_subfunctor {T : BigFppfOver B (Spec (.of k)) hk}
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    ξ ∈ degreeZeroAddSubgroup B hX hk f hdim T ↔
      ξ ∈ (geomDegreeZeroSubfunctor B hX hk f hdim).obj (op T) :=
  Iff.rfl

/-- The residue-field subgroup is contained in `Pic⁰_{X/k}(T)`. -/
theorem fibrewiseDegreeZeroAddSubgroup_le (T : BigFppfOver B (Spec (.of k)) hk) :
    fibrewiseDegreeZeroAddSubgroup B hX hk f hdim T ≤ degreeZeroAddSubgroup B hX hk f hdim T :=
  fun _ h => isGeomFibrewiseDegreeZero_of_isFibrewiseDegreeZero B hX hk f hdim h

/-- The restriction maps between the groups `Pic⁰_{X/k}(T)`. -/
def degreeZeroMap {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T) :
    degreeZeroAddSubgroup B hX hk f hdim T →+ degreeZeroAddSubgroup B hX hk f hdim T' :=
  ((picardRestrictAddHom B hX hk f g).comp
    (degreeZeroAddSubgroup B hX hk f hdim T).subtype).codRestrict _
      fun ξ => isGeomFibrewiseDegreeZero_map B hX hk f hdim g ξ.2

/-- **The presheaf of groups `T ↦ Pic⁰_{X/k}(T)`** on the big fppf site over `k`, read
multiplicatively. -/
def degreeZeroGrpFunctor : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (Multiplicative (degreeZeroAddSubgroup B hX hk f hdim T.unop))
  map {T T'} g := GrpCat.ofHom (degreeZeroMap B hX hk f hdim g.unop).toMultiplicative
  map_id T := by
    ext ξ
    exact Subtype.ext ((picardFunctor B hX hk f).map_id_apply _ _)
  map_comp {T T' T''} g g' := by
    ext ξ
    exact Subtype.ext ((picardFunctor B hX hk f).map_comp_apply g g' _)

/-- **`G` is a Jacobian of `X` over `k`.** The group scheme `G` over `k` represents the
presheaf of groups `Pic⁰_{X/k}` of sections of the Picard sheaf of degree zero on every geometric
fibre: for every `T` of the site over `k`, the group `Hom_k(T, G)` is identified with
`Pic⁰_{X/k}(T)`, naturally in `T`; and `G` is an abelian variety. -/
structure IsJacobianOf (G : Grp (Over (Spec (.of k)))) where
  /-- `Hom_k(T, G) ≃* Pic⁰_{X/k}(T)`. -/
  homMulEquiv (T : BigFppfOver B (Spec (.of k)) hk) :
    ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ G.X) ≃*
      (degreeZeroGrpFunctor B hX hk f hdim).obj (op T)
  /-- Naturality in `T`. -/
  homMulEquiv_naturality {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    (a : (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ G.X) :
    homMulEquiv T' ((BigFppfOver.toOver B (Spec (.of k)) hk).map g ≫ a) =
      (degreeZeroGrpFunctor B hX hk f hdim).map g.op (homMulEquiv T a)
  /-- The group scheme `G` is an abelian variety ([Stacks, Tag 03RO]). -/
  isAbelianVariety : IsAbelianVariety k G.X

end DegreeZero

end Jacobian

end ArithmeticOfJacobiPolynomials
