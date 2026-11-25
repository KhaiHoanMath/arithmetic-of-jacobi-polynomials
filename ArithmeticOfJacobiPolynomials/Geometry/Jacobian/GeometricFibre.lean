module

public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.ResidueDegree

/-!
# Geometric points of test schemes, and `Pic⁰` over an algebraically closed field

For a point `t` of a test scheme `T` of a big fppf site over `k`, the spectrum of an algebraic
closure `κ(t)‾` of the residue field lies in the site again (an algebraic extension is no larger
than `max ℵ₀ #κ(t)`), so `Spec κ(t)‾ ⟶ Spec κ(t) ⟶ T` is a geometric point of `T` in the site.

Over an algebraically closed ground field `k` the curve has a rational point, the degree of a
section of the Picard sheaf at a point is defined (`Stacks.PicardFunctor.residueDegree`) and is
unchanged by extension of the residue field (`Stacks.PicardFunctor.residueDegree_map`). Testing
at the geometric point over `t` then shows that the geometric-fibre condition of
`ArithmeticOfJacobiPolynomials.Jacobian.IsGeomFibrewiseDegreeZero` and the residue-field condition
`Stacks.PicardFunctor.IsFibrewiseDegreeZero` agree.

## Main results

* `ArithmeticOfJacobiPolynomials.Jacobian.contains_spec_algebraicClosure_residueField`: the size
  bound.
* `ArithmeticOfJacobiPolynomials.Jacobian.geomResidueTest`,
  `ArithmeticOfJacobiPolynomials.Jacobian.geomResidueTestπ`: the geometric point over `t`.
* `ArithmeticOfJacobiPolynomials.Jacobian.isGeomFibrewiseDegreeZero_iff_of_isAlgClosed` and
  `ArithmeticOfJacobiPolynomials.Jacobian.mem_degreeZeroAddSubgroup_iff_of_isAlgClosed`: over an
  algebraically closed field, `Pic⁰_{X/k}(T)` is the Stacks subfunctor
  `Stacks.PicardFunctor.degreeZeroSubfunctor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.PicardFunctor

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Jacobian

/-- **The spectrum of an algebraic closure of a residue field of a scheme of a big fppf site lies
in the site.** `Spec κ(y)` does ([Stacks, Tag 000R]), the algebraic closure has cardinality at
most `max #κ(y) ℵ₀` (Mathlib's `Algebra.IsAlgebraic.cardinalMk_le_max`, [Stacks, Tag 09GK]), and
the size of `Spec R` is `max ℵ₀ #R`. (The same argument appears in Stacks as a private lemma of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingRegular`, and for `Spec k` in
`AlgebraicGeometry.BigFppfSite.contains_spec_algebraicClosure`.) -/
theorem contains_spec_algebraicClosure_residueField (B : BigFppfSite.{u}) {Y : Scheme.{u}}
    (hY : B.Contains Y) (y : Y) :
    B.Contains (Spec (.of (AlgebraicClosure (Y.residueField y)))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (B.residueField_spec_contains hY y)
    ((Algebra.IsAlgebraic.cardinalMk_le_max _ _).trans_eq (max_comm _ _))

section GeometricResidue

variable (B : BigFppfSite.{u}) {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  (T : BigFppfOver B (Spec (.of k)) hk) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T)

/-- The algebraic closure `κ(t)‾` of the residue field at a point of a test scheme. -/
abbrev geomResidueField : Type u :=
  AlgebraicClosure (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)

/-- **The geometric point over `t`**: the test scheme `Spec κ(t)‾` with structure morphism
`Spec κ(t)‾ ⟶ Spec κ(t) ⟶ Spec k`. -/
abbrev geomResidueTest : BigFppfOver B (Spec (.of k)) hk :=
  geomTest B hk (geomResidueField B hk T t)
    (contains_spec_algebraicClosure_residueField B T.left.property t)
    (Spec.map (CommRingCat.ofHom (algebraMap
        (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
        (geomResidueField B hk T t))) ≫
      B.inclusion.map (residueTest B hk T t).hom)

/-- The morphism `Spec κ(t)‾ ⟶ Spec κ(t)` of test schemes. -/
def geomResidueTestπ : geomResidueTest B hk T t ⟶ residueTest B hk T t :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
    (geomResidueField B hk T t))))) rfl

/-- Every point of `Spec κ(t)` maps to `t`. -/
theorem toScheme_map_residueTestι_apply
    (y : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (residueTest B hk T t)) :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (residueTestι B hk T t) y = t := by
  change ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).fromSpecResidueField t y = t
  exact Scheme.fromSpecResidueField_apply t y

end GeometricResidue

section AlgClosed

variable (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (k : Type u) [Field k]
  [IsAlgClosed k] {hk : B.Contains (Spec (.of k))} (g : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
  [Smooth (B.inclusion.map g)]

/-- **Over an algebraically closed field the geometric-fibre condition implies the residue-field
condition.** For `t ∈ T`, test at the geometric point `Spec κ(t)‾ ⟶ T`: the degree of `ξ` at `t`
is the degree of its pullback at the point of `Spec κ(t)‾` by
`Stacks.PicardFunctor.residueDegree_map`, so it vanishes. -/
theorem isFibrewiseDegreeZero_of_isGeomFibrewiseDegreeZero (hdim : topologicalKrullDim X ≤ 1)
    {T : BigFppfOver B (Spec (.of k)) hk} {ξ : (picardFunctor B hX hk g).obj (op T)}
    (h : IsGeomFibrewiseDegreeZero B hX hk g hdim T ξ) :
    IsFibrewiseDegreeZero B hX hk g hdim T ξ := by
  refine (mem_degreeZeroSubfunctor_iff_residueDegree B hX k g T ξ).2 ?_
  intro t
  let e := geomResidueTestπ B hk T t ≫ residueTestι B hk T t
  let y : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (geomResidueTest B hk T t) :=
    IsLocalRing.closedPoint (geomResidueField B hk T t)
  have hξ := h (geomResidueField B hk T t)
    (contains_spec_algebraicClosure_residueField B T.left.property t) _ e
  have hy := (mem_degreeZeroSubfunctor_iff_residueDegree B hX k g (geomResidueTest B hk T t)
    ((picardFunctor B hX hk g).map e.op ξ)).1 hξ y
  have ht : (BigFppfOver.toScheme B (Spec (.of k)) hk).map e y = t := by
    rw [show e = geomResidueTestπ B hk T t ≫ residueTestι B hk T t from rfl, Functor.map_comp]
    exact toScheme_map_residueTestι_apply B hk T t _
  have he := residueDegree_map B hX k g e ξ y
  rw [ht] at he
  exact he.symm.trans hy

/-- **Over an algebraically closed field, `Pic⁰_{X/k}` is the Stacks subfunctor**: the
geometric-fibre and residue-field degree-zero conditions agree. -/
theorem isGeomFibrewiseDegreeZero_iff_of_isAlgClosed (hdim : topologicalKrullDim X ≤ 1)
    {T : BigFppfOver B (Spec (.of k)) hk} (ξ : (picardFunctor B hX hk g).obj (op T)) :
    IsGeomFibrewiseDegreeZero B hX hk g hdim T ξ ↔ IsFibrewiseDegreeZero B hX hk g hdim T ξ :=
  ⟨isFibrewiseDegreeZero_of_isGeomFibrewiseDegreeZero B hX k g hdim,
    isGeomFibrewiseDegreeZero_of_isFibrewiseDegreeZero B hX hk g hdim⟩

/-- `Pic⁰_{X/k}(T)` (geometric fibres) is the value at `T` of the Stacks subfunctor
`Stacks.PicardFunctor.degreeZeroSubfunctor` when `k` is algebraically closed. -/
theorem mem_degreeZeroAddSubgroup_iff_of_isAlgClosed (hdim : topologicalKrullDim X ≤ 1)
    {T : BigFppfOver B (Spec (.of k)) hk} (ξ : (picardFunctor B hX hk g).obj (op T)) :
    ξ ∈ degreeZeroAddSubgroup B hX hk g hdim T ↔
      ξ ∈ (degreeZeroSubfunctor B hX hk g hdim).obj (op T) :=
  isGeomFibrewiseDegreeZero_iff_of_isAlgClosed B hX k g hdim ξ

end AlgClosed

end Jacobian

end ArithmeticOfJacobiPolynomials
