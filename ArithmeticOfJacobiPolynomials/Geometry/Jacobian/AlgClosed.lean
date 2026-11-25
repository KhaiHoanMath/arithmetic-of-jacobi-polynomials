/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Unconditional

/-!
# The Jacobian over an algebraically closed field is the Stacks component `Pic⁰_{X/k}`

Let `k` be an algebraically closed field and `X ⟶ Spec k` a smooth projective curve in a big fppf
site `B`. Stacks proves that the Picard functor is represented by a scheme `P`
([Stacks, Tag 0B9Z]) and that the open and closed subscheme `P⁰` where the degree vanishes is an
open subgroup scheme which is an abelian variety of dimension `genus X` ([Stacks, Tag 0BA0]).
This file shows that this is a Jacobian in the sense of
`ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf`
(which does not mention a rational point). `IsJacobianOf` represents the geometric-fibre
`Pic⁰_{X/k}`; over an algebraically closed `k` it is the Stacks subfunctor
`Stacks.PicardFunctor.degreeZeroSubfunctor` that `P⁰` represents
(`ArithmeticOfJacobiPolynomials.Jacobian.mem_degreeZeroAddSubgroup_iff_of_isAlgClosed`):

* `ArithmeticOfJacobiPolynomials.Jacobian.nonempty_isJacobianOf_degreeZeroOpenSubgroupScheme`: for
any representing
  object `P` of `Pic_{X/k}`, the group scheme
  `Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme` represents `Pic⁰_{X/k}` as a presheaf of
  groups on the site, and is an abelian variety;
* `ArithmeticOfJacobiPolynomials.Jacobian.exists_isJacobianOf_of_isAlgClosed`: a Jacobian exists,
and it is an
  abelian variety of dimension `genus X` (`AlgebraicGeometry.genus`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite Stacks.PicardFunctor

open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Jacobian

attribute [local instance] bigFppfOverCartesianMonoidal toOverMonoidal

variable (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (k : Type u) [Field k]
  [IsAlgClosed k] {hk : B.Contains (Spec (.of k))} (g : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
  [Smooth (B.inclusion.map g)] {P : BigFppfOver B (Spec (.of k)) hk}
  (R : (picardFunctor B hX hk g).RepresentableBy P)

/-- **`Pic⁰_{X/k}` is a Jacobian of `X`** (over an algebraically closed field): the open subgroup
scheme `Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme` of the Picard scheme `P` represents
the presheaf of groups `T ↦ Pic⁰_{X/k}(T)` on the big fppf site, and is an abelian variety
([Stacks, Tags 0B9Z, 0BA0]). -/
theorem nonempty_isJacobianOf_degreeZeroOpenSubgroupScheme :
    Nonempty (IsJacobianOf B hX hk g (topologicalKrullDim_le_one_of_curve B hX k g)
      (degreeZeroOpenSubgroupScheme B hX k g R).carrier) := by
  let := grpObjOfRepresentableBy R
  let := representingGrpObj R
  obtain ⟨e, he⟩ := exists_iso_degreeZeroOpenSubgroupScheme B hX k g R
  let K := degreeZeroOpenSubgroupScheme B hX k g R
  have he' : degreeZeroOverHom B hX k g R = e.hom ≫ K.ι.hom.hom := he
  have hmono : Mono K.ι.hom.hom := by
    have := K.isOpenImmersion
    exact Over.mono_of_mono_left _
  let ff := fullyFaithfulToOver B hk
  -- the underlying function `Hom_k(T, J) → Pic⁰_{X/k}(T)`
  have key : ∀ (T : BigFppfOver B (Spec (.of k)) hk)
      (a : (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ K.carrier.X),
      ∃ b : T ⟶ degreeZeroObj B hX k g R,
        b ≫ degreeZeroHom B hX k g R = ff.preimage (a ≫ K.ι.hom.hom) := by
    intro T a
    refine ⟨ff.preimage (a ≫ e.inv), ff.map_injective ?_⟩
    rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage]
    change _ ≫ degreeZeroOverHom B hX k g R = _
    rw [he', Category.assoc, e.inv_hom_id_assoc]
  have mem : ∀ (T : BigFppfOver B (Spec (.of k)) hk)
      (a : (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ K.carrier.X),
      R.homEquiv (ff.preimage (a ≫ K.ι.hom.hom)) ∈
        degreeZeroAddSubgroup B hX hk g (topologicalKrullDim_le_one_of_curve B hX k g) T := by
    intro T a
    refine (mem_degreeZeroAddSubgroup_iff_of_isAlgClosed B hX k g _ _).2 ?_
    refine (exists_comp_degreeZeroHom_iff_mem_degreeZeroSubfunctor B hX k g R _).1 ?_
    obtain ⟨b, hb⟩ := key T a
    exact ⟨b, hb⟩
  let Φ : ∀ T : BigFppfOver B (Spec (.of k)) hk,
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ K.carrier.X) →
        (degreeZeroGrpFunctor B hX hk g (topologicalKrullDim_le_one_of_curve B hX k g)).obj
          (op T) :=
    fun T a => Multiplicative.ofAdd ⟨R.homEquiv (ff.preimage (a ≫ K.ι.hom.hom)), mem T a⟩
  have Φ_mul : ∀ (T : BigFppfOver B (Spec (.of k)) hk)
      (a b : (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ K.carrier.X),
      Φ T (a * b) = Φ T a * Φ T b := by
    intro T a b
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change R.homEquiv (ff.preimage ((a * b) ≫ K.ι.hom.hom)) = R.homEquiv (ff.preimage
      (a ≫ K.ι.hom.hom)) + R.homEquiv (ff.preimage (b ≫ K.ι.hom.hom))
    rw [MonObj.mul_comp, ← RepresentableBy.homEquiv_mul]
    congr 1
    exact (ff.homMulEquiv (X := T) (M := P)).symm.map_mul _ _
  have Φ_bij : ∀ T : BigFppfOver B (Spec (.of k)) hk, Function.Bijective (Φ T) := by
    intro T
    constructor
    · intro a a' h
      have h1 := congrArg (fun z => (Multiplicative.toAdd z).1) h
      change R.homEquiv (ff.preimage (a ≫ K.ι.hom.hom)) =
        R.homEquiv (ff.preimage (a' ≫ K.ι.hom.hom)) at h1
      have h2 := congrArg (BigFppfOver.toOver B (Spec (.of k)) hk).map (R.homEquiv.injective h1)
      rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage] at h2
      exact (cancel_mono K.ι.hom.hom).1 h2
    · intro ξ
      have hξ := (exists_comp_degreeZeroHom_iff_mem_degreeZeroSubfunctor B hX k g R
        (R.homEquiv.symm (Multiplicative.toAdd ξ).1)).2 (by
          rw [Equiv.apply_symm_apply]
          exact (mem_degreeZeroAddSubgroup_iff_of_isAlgClosed B hX k g _ _).1
            (Multiplicative.toAdd ξ).2)
      obtain ⟨b, hb⟩ := hξ
      refine ⟨(BigFppfOver.toOver B (Spec (.of k)) hk).map b ≫ e.hom, ?_⟩
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change R.homEquiv (ff.preimage (((BigFppfOver.toOver B (Spec (.of k)) hk).map b ≫ e.hom) ≫
        K.ι.hom.hom)) = _
      rw [Category.assoc, ← he']
      change R.homEquiv (ff.preimage ((BigFppfOver.toOver B (Spec (.of k)) hk).map
        (b ≫ degreeZeroHom B hX k g R))) = _
      rw [hb, Functor.FullyFaithful.preimage_map, Equiv.apply_symm_apply]
  refine
    ⟨{ homMulEquiv := fun T => MulEquiv.ofBijective (MonoidHom.mk' (Φ T) (Φ_mul T)) (Φ_bij T)
       homMulEquiv_naturality := ?_
       isAbelianVariety := (isAbelianVariety_degreeZeroOpenSubgroupScheme B hX k g R).1 }⟩
  intro T T' φ a
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change R.homEquiv (ff.preimage (((BigFppfOver.toOver B (Spec (.of k)) hk).map φ ≫ a) ≫
    K.ι.hom.hom)) = (picardFunctor B hX hk g).map φ.op (R.homEquiv (ff.preimage
      (a ≫ K.ι.hom.hom)))
  have : ff.preimage (((BigFppfOver.toOver B (Spec (.of k)) hk).map φ ≫ a) ≫ K.ι.hom.hom) =
      φ ≫ ff.preimage (a ≫ K.ι.hom.hom) := by
    apply ff.map_injective
    rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage,
      Category.assoc]
  rw [this, R.homEquiv_comp]

omit R in
/-- **Existence of the Jacobian over an algebraically closed field** ([Stacks, Tags 0B9Z, 0BA0]):
a smooth projective curve `X` over an algebraically closed field `k`, in a big fppf site, has a
Jacobian `G` in the sense of `IsJacobianOf` (an abelian variety representing `Pic⁰_{X/k}`), and
every such `G` constructed this way has dimension `genus X`. -/
theorem exists_isJacobianOf_of_isAlgClosed :
    ∃ G : Grp (Over (Spec (.of k))),
      Nonempty (IsJacobianOf B hX hk g (topologicalKrullDim_le_one_of_curve B hX k g) G) ∧
        Stacks.Groupoids.abelianVarietyDimension G.X = genus (B.inclusion.map g) := by
  obtain ⟨P, ⟨R⟩⟩ := isRepresentable_picardFunctor_of_isAlgClosed B hX hk (B.inclusion.map g)
  let := representingGrpObj R
  exact ⟨_, nonempty_isJacobianOf_degreeZeroOpenSubgroupScheme B hX k g R,
    (isAbelianVariety_degreeZeroOpenSubgroupScheme B hX k g R).2⟩

end Jacobian

end ArithmeticOfJacobiPolynomials
