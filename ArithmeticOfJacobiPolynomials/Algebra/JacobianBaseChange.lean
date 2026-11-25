/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.JacobianUniqueness
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.AlgebraicGeometry.PicardScheme.BaseChangePullback
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardBasePoints
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.DegreeIso
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.FibreDegree
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.RepresentingGroup
public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product

/-!
# Base change of the relative Picard functor along a field extension

Let `K/k` be an extension of fields, `B` a big fppf site containing `X`, `Spec k`, `Spec K` and a
cartesian square `X_K = X ×_k K`. Every `K`-scheme `T` of the site is a `k`-scheme by composition
with `Spec K ⟶ Spec k` (the functor `F = Over.map ι` of slices of the site), and the base changes
agree: `X_K ×_K T = X ×_k T`. This file shows that the Picard functor `Pic_{X_K/K}` of the base
changed curve is the restriction along `F` of the Picard functor `Pic_{X/k}`
(`Stacks.PicardFunctor.picardFunctor`, [Stacks, Tag 0B9L]):

`Pic_{X_K/K}(T) ≃+ Pic_{X/k}(T)`, naturally in the `K`-scheme `T`.

The proof sheafifies the isomorphism of presheaves `T ↦ Pic(X_K ×_K T) ≅ Pic(X ×_k T)`; the
compatibility of fppf sheafification with the restriction functor `F` (continuous and
cocontinuous) is Mathlib's
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`.
The identification is carried out for the Picard functor formed in abelian groups, so that it is
additive by construction, and transported to `Stacks.PicardFunctor.picardFunctor` through
`Stacks.PicardFunctor.picardFunctorAddEquiv`.

## Main definitions

* `ArithmeticOfJacobiPolynomials.Jacobian.BaseChange.restrictSite`: the functor `F`.
* `ArithmeticOfJacobiPolynomials.Jacobian.BaseChange.picardAddEquiv`: `Pic_{X_K/K}(T) ≃+
Pic_{X/k}(F T)`.

## Main results

* `ArithmeticOfJacobiPolynomials.Jacobian.BaseChange.picardAddEquiv_naturality` and
  `ArithmeticOfJacobiPolynomials.Jacobian.BaseChange.picardAddEquiv_toPicardFunctor`.
* `ArithmeticOfJacobiPolynomials.Jacobian.BaseChange.isGeomFibrewiseDegreeZero_picardAddEquiv_iff`:
  the geometric-fibre degree-zero conditions (defining `Pic⁰`) correspond. A geometric point
  `Spec Ω ⟶ T` of a `K`-scheme `T`, regarded over `k`, is a geometric point of `T` regarded over
  `k`, and conversely every `k`-morphism `Spec Ω ⟶ T` is a `K`-morphism for the composite
  structure map `Spec Ω ⟶ T ⟶ Spec K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.PicardFunctor

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Jacobian

namespace BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (B : BigFppfSite.{u})
  {X : Scheme.{u}} (hX : B.Contains X) (hk : B.Contains (Spec (.of k)))
  (hK : B.Contains (Spec (.of K))) (f : B.obj hX ⟶ B.obj hk)
  {XK : Scheme.{u}} (hXK : B.Contains XK) (fK : B.obj hXK ⟶ B.obj hK)

section Generic

variable {S : Scheme.{u}} {Y : Scheme.{u}} (hY : B.Contains Y) (hS : B.Contains S)
  (h : B.obj hY ⟶ B.obj hS)

@[reassoc (attr := simp)]
theorem baseChangeMap_fst {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    Stacks.PicardFunctor.baseChangeMap B hY hS h g ≫
        pullback.fst (B.inclusion.map h) (B.inclusion.map U.hom) =
      pullback.fst (B.inclusion.map h) (B.inclusion.map T.hom) := by
  simp [Stacks.PicardFunctor.baseChangeMap, pullback.map]

@[reassoc (attr := simp)]
theorem baseChangeMap_snd {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    Stacks.PicardFunctor.baseChangeMap B hY hS h g ≫
        pullback.snd (B.inclusion.map h) (B.inclusion.map U.hom) =
      pullback.snd (B.inclusion.map h) (B.inclusion.map T.hom) ≫ B.inclusion.map g.left := by
  simp [Stacks.PicardFunctor.baseChangeMap, pullback.map]

end Generic

/-- The morphism `Spec K ⟶ Spec k` of an extension of fields. -/
abbrev specMap (k K : Type u) [Field k] [Field K] [Algebra k K] : Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The morphism `Spec K ⟶ Spec k` as a morphism of the site. -/
def siteMap : B.obj hK ⟶ B.obj hk := ObjectProperty.homMk (specMap k K)

/-- **Regarding a `K`-scheme of the site as a `k`-scheme.** -/
abbrev restrictSite : BigFppfOver B (Spec (.of K)) hK ⥤ BigFppfOver B (Spec (.of k)) hk :=
  Over.map (siteMap B hk hK)

variable {B hX hk hK f hXK fK}
  (gK : XK ⟶ X)
  (hsq : IsPullback gK (B.inclusion.map fK) (B.inclusion.map f)
    (B.inclusion.map (siteMap B hk hK)))

include hsq in
/-- The base change `X_K ×_K T` of the base-changed curve is the base change `X ×_k T`. -/
theorem isPullback_bc (T : BigFppfOver B (Spec (.of K)) hK) :
    IsPullback (pullback.fst (B.inclusion.map fK) (B.inclusion.map T.hom) ≫ gK)
      (pullback.snd (B.inclusion.map fK) (B.inclusion.map T.hom))
      (B.inclusion.map f)
      (B.inclusion.map ((restrictSite B hk hK).obj T).hom) :=
  (IsPullback.of_hasPullback (B.inclusion.map fK) (B.inclusion.map T.hom)).paste_horiz hsq

/-- The canonical isomorphism `X_K ×_K T ≅ X ×_k T` of base changes. -/
def bcIso (T : BigFppfOver B (Spec (.of K)) hK) :
    baseChange B hXK hK fK T ≅ baseChange B hX hk f ((restrictSite B hk hK).obj T) :=
  (isPullback_bc gK hsq T).isoPullback

@[reassoc (attr := simp)]
theorem bcIso_hom_fst (T : BigFppfOver B (Spec (.of K)) hK) :
    (bcIso gK hsq T).hom ≫ pullback.fst _ _ =
      pullback.fst (B.inclusion.map fK) (B.inclusion.map T.hom) ≫ gK :=
  (isPullback_bc gK hsq T).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem bcIso_hom_snd (T : BigFppfOver B (Spec (.of K)) hK) :
    (bcIso gK hsq T).hom ≫ pullback.snd _ _ =
      pullback.snd (B.inclusion.map fK) (B.inclusion.map T.hom) :=
  (isPullback_bc gK hsq T).isoPullback_hom_snd

/-- The comparison isomorphisms `X_K ×_K T ≅ X ×_k T` are natural in the `K`-scheme `T`. -/
theorem baseChangeMap_bcIso_hom {T U : BigFppfOver B (Spec (.of K)) hK} (g : T ⟶ U) :
    Stacks.PicardFunctor.baseChangeMap B hXK hK fK g ≫ (bcIso gK hsq U).hom =
      (bcIso gK hsq T).hom ≫
        Stacks.PicardFunctor.baseChangeMap B hX hk f ((restrictSite B hk hK).map g) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcIso_hom_fst, baseChangeMap_fst, baseChangeMap_fst_assoc]
  · simp only [Category.assoc, bcIso_hom_snd, baseChangeMap_snd,
      bcIso_hom_snd_assoc, Over.map_map_left]

theorem bcIso_inv_baseChangeMap {T U : BigFppfOver B (Spec (.of K)) hK} (g : T ⟶ U) :
    Stacks.PicardFunctor.baseChangeMap B hX hk f ((restrictSite B hk hK).map g) ≫
        (bcIso gK hsq U).inv =
      (bcIso gK hsq T).inv ≫ Stacks.PicardFunctor.baseChangeMap B hXK hK fK g := by
  refine (cancel_epi (bcIso gK hsq T).hom).1 ?_
  rw [← Category.assoc, ← baseChangeMap_bcIso_hom gK hsq g, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

/-- **The Picard presheaves of the two base changes are isomorphic**, as presheaves of abelian
groups on the `K`-schemes of the site: `Pic(X_K ×_K T) ≅ Pic(X ×_k T)`. -/
def picardAddPresheafIso :
    picardAddPresheaf B hXK hK fK ≅
      (restrictSite B hk hK).op ⋙ picardAddPresheaf B hX hk f :=
  NatIso.ofComponents
    (fun T =>
      (Stacks.Picard.schemePullbackClassAddEquiv (bcIso gK hsq T.unop).symm).toAddCommGrpIso)
    (fun {T U} g => by
      ext x
      change Stacks.Picard.schemePullbackClass (bcIso gK hsq U.unop).inv
          (Stacks.Picard.schemePullbackClass
            (Stacks.PicardFunctor.baseChangeMap B hXK hK fK g.unop) x) =
        Stacks.Picard.schemePullbackClass (Stacks.PicardFunctor.baseChangeMap B hX hk f
          ((restrictSite B hk hK).map g.unop))
          (Stacks.Picard.schemePullbackClass (bcIso gK hsq T.unop).inv x)
      refine (Stacks.Picard.schemePullbackClass_comp _ _ x).trans
        (Eq.trans ?_ (Stacks.Picard.schemePullbackClass_comp _ _ x).symm)
      exact congrArg (fun m => Stacks.Picard.schemePullbackClass m x)
        (bcIso_inv_baseChangeMap gK hsq g.unop).symm)

/-! ### Sheafification -/

/-- **The Picard functors of the two base changes agree** (in abelian groups): sheafification
commutes with restriction along `restrictSite`, which is continuous and cocontinuous for the fppf
topologies (Mathlib's `Functor.pushforwardContinuousSheafificationCompatibility`). -/
def picardAddFunctorIso :
    picardAddFunctor B hXK hK fK ≅ (restrictSite B hk hK).op ⋙ picardAddFunctor B hX hk f :=
  (presheafToSheaf (BigFppfOver.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1} ⋙
      sheafToPresheaf _ _).mapIso (picardAddPresheafIso gK hsq) ≪≫
    (sheafToPresheaf _ _).mapIso
      (((restrictSite B hk hK).pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat.{u + 1} (BigFppfOver.topology B (Spec (.of K)) hK)
        (BigFppfOver.topology B (Spec (.of k)) hk)).app (picardAddPresheaf B hX hk f))

theorem toPicardAddFunctor_picardAddFunctorIso :
    toPicardAddFunctor B hXK hK fK ≫ (picardAddFunctorIso gK hsq).hom =
      (picardAddPresheafIso gK hsq).hom ≫
        Functor.whiskerLeft (restrictSite B hk hK).op (toPicardAddFunctor B hX hk f) := by
  have h1 := toSheafify_naturality (BigFppfOver.topology B (Spec (.of K)) hK)
    (picardAddPresheafIso gK hsq).hom
  have h2 := (restrictSite B hk hK).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{u + 1} (BigFppfOver.topology B (Spec (.of K)) hK)
    (BigFppfOver.topology B (Spec (.of k)) hk) (picardAddPresheaf B hX hk f)
  change toSheafify _ _ ≫ (sheafifyMap _ _ ≫ _) = _
  rw [← Category.assoc, ← h1, Category.assoc]
  exact congrArg (fun m => (picardAddPresheafIso gK hsq).hom ≫ m) h2

theorem picardFunctorAddEquiv_map {S Y : Scheme.{u}} (hY : B.Contains Y) (hS : B.Contains S)
    (h : B.obj hY ⟶ B.obj hS) {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (ξ : (picardFunctor B hY hS h).obj (op U)) :
    picardFunctorAddEquiv B hY hS h T ((picardFunctor B hY hS h).map g.op ξ) =
      (picardAddFunctor B hY hS h).map g.op (picardFunctorAddEquiv B hY hS h U ξ) :=
  ConcreteCategory.congr_hom ((picardFunctorIsoPicardAddFunctor B hY hS h).hom.naturality g.op) ξ

/-- **`Pic_{X_K/K}(T) ≃+ Pic_{X/k}(T)`** for a `K`-scheme `T` of the site (regarded as a
`k`-scheme through `restrictSite`). -/
def picardAddEquiv (T : BigFppfOver B (Spec (.of K)) hK) :
    (picardFunctor B hXK hK fK).obj (op T) ≃+
      (picardFunctor B hX hk f).obj (op ((restrictSite B hk hK).obj T)) :=
  (picardFunctorAddEquiv B hXK hK fK T).trans
    (((picardAddFunctorIso gK hsq).app (op T)).addCommGroupIsoToAddEquiv.trans
      (picardFunctorAddEquiv B hX hk f ((restrictSite B hk hK).obj T)).symm)

/-- The identification of Picard functors sends the class of an invertible module on
`X_K ×_K T` to the class of its transport to `X ×_k T`. -/
theorem picardAddEquiv_toPicardFunctor (T : BigFppfOver B (Spec (.of K)) hK)
    (c : picardAt B hXK hK fK T) :
    picardAddEquiv gK hsq T ((toPicardFunctor B hXK hK fK).app (op T) c) =
      (toPicardFunctor B hX hk f).app (op ((restrictSite B hk hK).obj T))
        (Stacks.Picard.schemePullbackClass (bcIso gK hsq T).inv c) := by
  apply (picardFunctorAddEquiv B hX hk f _).injective
  simp only [picardAddEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [picardFunctorAddEquiv_toPicardFunctor, picardFunctorAddEquiv_toPicardFunctor]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toPicardAddFunctor_picardAddFunctorIso gK hsq) (op T)) c
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  exact h

/-- The identification of Picard functors is natural in the `K`-scheme `T`. -/
theorem picardAddEquiv_map {T T' : BigFppfOver B (Spec (.of K)) hK} (g : T' ⟶ T)
    (ξ : (picardFunctor B hXK hK fK).obj (op T)) :
    picardAddEquiv gK hsq T' ((picardFunctor B hXK hK fK).map g.op ξ) =
      (picardFunctor B hX hk f).map ((restrictSite B hk hK).map g).op
        (picardAddEquiv gK hsq T ξ) := by
  apply (picardFunctorAddEquiv B hX hk f _).injective
  simp only [picardAddEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [picardFunctorAddEquiv_map, picardFunctorAddEquiv_map, AddEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom ((picardAddFunctorIso gK hsq).hom.naturality g.op)
    (picardFunctorAddEquiv B hXK hK fK T ξ)

/-! ### The fibrewise degree-zero condition -/

/-- **A geometric test scheme over `K`, regarded over `k`**, is the geometric test scheme over `k`
with the composite structure morphism `Spec Ω ⟶ Spec K ⟶ Spec k`. -/
def geomTestRestrictIso (Ω : Type u) [Field Ω] (hΩ : B.Contains (Spec (.of Ω)))
    {s : Spec (.of Ω) ⟶ Spec (.of k)} {s' : Spec (.of Ω) ⟶ Spec (.of K)}
    (hs : s' ≫ specMap k K = s) :
    geomTest B hk Ω hΩ s ≅ (restrictSite B hk hK).obj (geomTest B hK Ω hΩ s') :=
  Over.isoMk (Iso.refl _) (by
    apply B.inclusion.map_injective
    simpa [siteMap] using hs)

section DegreeZero

variable [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)]
  (hdim : topologicalKrullDim X ≤ 1) (hdimK : topologicalKrullDim XK ≤ 1)
  (T : BigFppfOver B (Spec (.of K)) hK) (t : (BigFppfOver.toScheme B (Spec (.of K)) hK).obj T)

/-- The two residue test schemes at a point `t` of a `K`-scheme `T` agree: `Spec κ(t)` over
`Spec k`. -/
def residueIso : (restrictSite B hk hK).obj (residueTest B hK T t) ≅
    residueTest B hk ((restrictSite B hk hK).obj T) t :=
  Over.isoMk (Iso.refl _) (by
    apply B.inclusion.map_injective
    simp [Category.assoc])

@[simp]
theorem residueIso_inv_left : (residueIso (hk := hk) T t).inv.left = 𝟙 _ := rfl

/-- The comparison isomorphism `X ×_k Spec κ(t) ≅ X_K ×_K Spec κ(t)`. -/
def residueTransportMap :
    baseChange B hX hk f (residueTest B hk ((restrictSite B hk hK).obj T) t) ⟶
      baseChange B hXK hK fK (residueTest B hK T t) :=
  Stacks.PicardFunctor.baseChangeMap B hX hk f (residueIso (hk := hk) T t).inv ≫
    (bcIso gK hsq (residueTest B hK T t)).inv

instance : IsIso (residueTransportMap (hk := hk) gK hsq T t) := by
  have : IsIso (Stacks.PicardFunctor.baseChangeMap B hX hk f (residueIso (hk := hk) T t).inv) :=
    ⟨⟨Stacks.PicardFunctor.baseChangeMap B hX hk f (residueIso (hk := hk) T t).hom, by
      rw [← Stacks.PicardFunctor.baseChangeMap_comp, Iso.inv_hom_id,
        Stacks.PicardFunctor.baseChangeMap_id], by
      rw [← Stacks.PicardFunctor.baseChangeMap_comp, Iso.hom_inv_id,
        Stacks.PicardFunctor.baseChangeMap_id]⟩⟩
  exact inferInstanceAs (IsIso (_ ≫ _))

/-- Transport of line bundles on `X_K ×_K Spec κ(t)` to `X ×_k Spec κ(t)`. -/
def residueTransport :
    picardAt B hXK hK fK (residueTest B hK T t) →+
      picardAt B hX hk f (residueTest B hk ((restrictSite B hk hK).obj T) t) :=
  Stacks.Picard.schemePullbackClassHom (residueTransportMap (hk := hk) gK hsq T t)

omit [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)] in
theorem toPicardFunctor_residueTransport
    (L : picardAt B hXK hK fK (residueTest B hK T t)) :
    (toPicardFunctor B hX hk f).app
        (op (residueTest B hk ((restrictSite B hk hK).obj T) t))
        (residueTransport gK hsq T t L) =
      (picardFunctor B hX hk f).map (residueIso (hk := hk) T t).inv.op
        (picardAddEquiv gK hsq (residueTest B hK T t)
          ((toPicardFunctor B hXK hK fK).app (op (residueTest B hK T t)) L)) := by
  rw [picardAddEquiv_toPicardFunctor]
  have h : residueTransport gK hsq T t L =
      picardMap B hX hk f (residueIso (hk := hk) T t).inv
        (Stacks.Picard.schemePullbackClass (bcIso gK hsq (residueTest B hK T t)).inv L) :=
    (Stacks.Picard.schemePullbackClass_comp _ _ L).symm
  rw [h]
  exact toPicardFunctor_app_naturality B hX hk f _ _

theorem residueTransport_degree (L : picardAt B hXK hK fK (residueTest B hK T t)) :
    Stacks.Picard.ofSchemeDegree
        (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj T).residueField t)
        (pullback.snd (B.inclusion.map f)
          (B.inclusion.map (residueTest B hk ((restrictSite B hk hK).obj T) t).hom))
        (topologicalKrullDim_baseChange_residueTest B hX hk f hdim
          ((restrictSite B hk hK).obj T) t)
        (residueTransport gK hsq T t L) =
      Stacks.Picard.ofSchemeDegree
        (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj T).residueField t)
        (pullback.snd (B.inclusion.map fK) (B.inclusion.map (residueTest B hK T t).hom))
        (topologicalKrullDim_baseChange_residueTest B hXK hK fK hdimK T t) L := by
  set E := residueTransportMap (hk := hk) gK hsq T t with hEdef
  have hE : E ≫ pullback.snd (B.inclusion.map fK) (B.inclusion.map (residueTest B hK T t).hom) =
      pullback.snd (B.inclusion.map f)
        (B.inclusion.map (residueTest B hk ((restrictSite B hk hK).obj T) t).hom) := by
    have h1 : (bcIso gK hsq (residueTest B hK T t)).inv ≫
        pullback.snd (B.inclusion.map fK) (B.inclusion.map (residueTest B hK T t).hom) =
        pullback.snd _ _ := by
      rw [Iso.inv_comp_eq]
      exact (bcIso_hom_snd gK hsq (residueTest B hK T t)).symm
    rw [hEdef, residueTransportMap, Category.assoc, h1, baseChangeMap_snd]
    simp
  have hproper : IsProper (E ≫ pullback.snd (B.inclusion.map fK)
      (B.inclusion.map (residueTest B hK T t).hom)) := by rw [hE]; infer_instance
  have h2 := Stacks.Picard.ofSchemeDegree_schemePullbackClass_of_isIso
    (((BigFppfOver.toScheme B (Spec (.of K)) hK).obj T).residueField t)
    (pullback.snd (B.inclusion.map fK) (B.inclusion.map (residueTest B hK T t).hom)) E
    (topologicalKrullDim_baseChange_residueTest B hXK hK fK hdimK T t)
    (topologicalKrullDim_baseChange_residueTest B hX hk f hdim ((restrictSite B hk hK).obj T) t) L
  refine Eq.trans ?_ h2
  exact Stacks.Picard.ofSchemeDegree_congr_structureMap _ hE.symm _ _

omit [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)] in
theorem residueIso_inv_comp :
    (residueIso (hk := hk) T t).inv ≫ (restrictSite B hk hK).map (residueTestι B hK T t) =
      residueTestι B hk ((restrictSite B hk hK).obj T) t := by
  ext1
  ext1
  rfl

omit [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)] in
theorem picardFunctor_map_residueIso_inv_injective :
    Function.Injective ((picardFunctor B hX hk f).map (residueIso (hk := hk) T t).inv.op) := by
  intro x y h
  have h' := congrArg ((picardFunctor B hX hk f).map (residueIso (hk := hk) T t).hom.op) h
  simpa [← Functor.map_comp_apply, ← op_comp] using h'

omit [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)] in
theorem residueTransport_surjective : Function.Surjective (residueTransport gK hsq T t) := by
  intro L'
  refine ⟨Stacks.Picard.schemePullbackClass (inv (residueTransportMap (hk := hk) gK hsq T t)) L',
    ?_⟩
  change Stacks.Picard.schemePullbackClass (residueTransportMap (hk := hk) gK hsq T t)
    (Stacks.Picard.schemePullbackClass (inv (residueTransportMap (hk := hk) gK hsq T t)) L') = L'
  rw [Stacks.Picard.schemePullbackClass_comp, IsIso.hom_inv_id,
    Stacks.Picard.schemePullbackClass_id]

omit [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)] in
theorem toPicardFunctor_residueIso
    (ξ : (picardFunctor B hXK hK fK).obj (op T)) :
    (picardFunctor B hX hk f).map (residueIso (hk := hk) T t).inv.op
        (picardAddEquiv gK hsq (residueTest B hK T t) ((picardFunctor B hXK hK fK).map
          (residueTestι B hK T t).op ξ)) =
      (picardFunctor B hX hk f).map
        (residueTestι B hk ((restrictSite B hk hK).obj T) t).op (picardAddEquiv gK hsq T ξ) := by
  rw [picardAddEquiv_map, ← Functor.map_comp_apply, ← op_comp, residueIso_inv_comp]

/-- **The fibrewise degree-zero conditions correspond** under `Pic_{X_K/K}(T) ≃+ Pic_{X/k}(T)`. -/
theorem isFibrewiseDegreeZero_picardAddEquiv_iff (ξ : (picardFunctor B hXK hK fK).obj (op T)) :
    IsFibrewiseDegreeZero B hXK hK fK hdimK T ξ ↔
      IsFibrewiseDegreeZero B hX hk f hdim ((restrictSite B hk hK).obj T)
        (picardAddEquiv gK hsq T ξ) := by
  constructor
  · intro h t
    obtain ⟨L, hL, hLξ⟩ := h t
    refine ⟨residueTransport gK hsq T t L, ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker] at hL ⊢
      exact (residueTransport_degree gK hsq hdim hdimK T t L).trans hL
    · rw [toPicardFunctor_residueTransport, hLξ]
      exact toPicardFunctor_residueIso gK hsq T t ξ
  · intro h t
    obtain ⟨L', hL', hL'ξ⟩ := h t
    obtain ⟨L, rfl⟩ := residueTransport_surjective gK hsq T t L'
    refine ⟨L, ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker] at hL' ⊢
      exact (residueTransport_degree gK hsq hdim hdimK T t L).symm.trans hL'
    · apply (picardAddEquiv gK hsq (residueTest B hK T t)).injective
      apply picardFunctor_map_residueIso_inv_injective (hk := hk) T t
      rw [← toPicardFunctor_residueTransport, hL'ξ]
      exact (toPicardFunctor_residueIso gK hsq T t ξ).symm

/-- **The geometric-fibre degree-zero conditions correspond** under
`Pic_{X_K/K}(T) ≃+ Pic_{X/k}(T)`: the conditions at a geometric point `Spec Ω` are the
residue-field conditions there (`isFibrewiseDegreeZero_picardAddEquiv_iff`), and the geometric
points of `T` over `K` and over `k` are the same morphisms. -/
theorem isGeomFibrewiseDegreeZero_picardAddEquiv_iff
    (ξ : (picardFunctor B hXK hK fK).obj (op T)) :
    IsGeomFibrewiseDegreeZero B hXK hK fK hdimK T ξ ↔
      IsGeomFibrewiseDegreeZero B hX hk f hdim ((restrictSite B hk hK).obj T)
        (picardAddEquiv gK hsq T ξ) := by
  constructor
  · intro h Ω _ _ hΩ s e
    -- The map to T determines the K-structure on Spec Ω.
    have hs : (B.inclusion.map e.left ≫ B.inclusion.map T.hom) ≫ specMap k K = s := by
      have hw := congrArg B.inclusion.map (Over.w e)
      simpa [siteMap, Category.assoc] using hw
    have hcomp : (geomTestRestrictIso (hk := hk) (hK := hK) Ω hΩ hs).hom ≫
        (restrictSite B hk hK).map (Over.homMk e.left rfl :
          geomTest B hK Ω hΩ (B.inclusion.map e.left ≫ B.inclusion.map T.hom) ⟶ T) = e := by
      ext1
      exact Category.id_comp e.left
    have H := h Ω hΩ _ (Over.homMk e.left rfl :
      geomTest B hK Ω hΩ (B.inclusion.map e.left ≫ B.inclusion.map T.hom) ⟶ T)
    rw [isFibrewiseDegreeZero_picardAddEquiv_iff gK hsq hdim hdimK, picardAddEquiv_map] at H
    have H2 := isFibrewiseDegreeZero_map B hX hk f hdim
      (geomTestRestrictIso (hk := hk) (hK := hK) Ω hΩ hs).hom H
    rwa [← Functor.map_comp_apply, ← op_comp, hcomp] at H2
  · intro h Ω _ _ hΩ s' e'
    rw [isFibrewiseDegreeZero_picardAddEquiv_iff gK hsq hdim hdimK, picardAddEquiv_map]
    have H := h Ω hΩ (s' ≫ specMap k K)
      ((geomTestRestrictIso (hk := hk) (hK := hK) Ω hΩ (s' := s')
        (rfl : s' ≫ specMap k K = s' ≫ specMap k K)).hom ≫ (restrictSite B hk hK).map e')
    have H2 := isFibrewiseDegreeZero_map B hX hk f hdim
      (geomTestRestrictIso (hk := hk) (hK := hK) Ω hΩ (s' := s')
        (rfl : s' ≫ specMap k K = s' ≫ specMap k K)).inv H
    rwa [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id_assoc] at H2

end DegreeZero

/-! ### The base-changed group and the base-changed Jacobian -/

section GroupBaseChange

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

variable [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)]
  (hdim : topologicalKrullDim X ≤ 1) (hdimK : topologicalKrullDim XK ≤ 1)

omit [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)] in
include hsq in
/-- The base change `X_K ⟶ Spec K` of a proper morphism is proper. -/
theorem isProper_of_isPullback_siteMap [IsProper (B.inclusion.map f)] :
    IsProper (B.inclusion.map fK) :=
  MorphismProperty.of_isPullback hsq ‹IsProper (B.inclusion.map f)›

omit [IsProper (B.inclusion.map fK)] in
include hsq in
/-- Extension of the base field does not change the dimension of a proper scheme. -/
theorem topologicalKrullDim_le_of_isPullback_siteMap (hdim : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim XK ≤ 1 := by
  have : LocallyOfFiniteType (B.inclusion.map f) := inferInstance
  have : Subsingleton (B.inclusion.obj (B.obj hk)) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have : Subsingleton (B.inclusion.obj (B.obj hK)) :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  have : Surjective (B.inclusion.map (siteMap B hk hK)) :=
    ⟨fun y => ⟨(default : Spec (.of K)), Subsingleton.elim _ _⟩⟩
  exact (topologicalKrullDim_eq_of_isPullback_of_subsingleton hsq).trans_le hdim

/-- **The group `Pic⁰`, compared.** The identification of the Picard functors restricts to an
isomorphism of the groups `Pic⁰_{X_K/K}(T) ≃+ Pic⁰_{X/k}(T)`. -/
def degreeZeroAddEquiv (T : BigFppfOver B (Spec (.of K)) hK) :
    degreeZeroAddSubgroup B hXK hK fK hdimK T ≃+
      degreeZeroAddSubgroup B hX hk f hdim ((restrictSite B hk hK).obj T) where
  toFun ξ := ⟨picardAddEquiv gK hsq T ξ.1,
    (isGeomFibrewiseDegreeZero_picardAddEquiv_iff gK hsq hdim hdimK T ξ.1).1 ξ.2⟩
  invFun ξ := ⟨(picardAddEquiv gK hsq T).symm ξ.1,
    (isGeomFibrewiseDegreeZero_picardAddEquiv_iff gK hsq hdim hdimK T _).2
      (by rw [AddEquiv.apply_symm_apply]; exact ξ.2)⟩
  left_inv ξ := Subtype.ext (AddEquiv.symm_apply_apply _ _)
  right_inv ξ := Subtype.ext (AddEquiv.apply_symm_apply _ _)
  map_add' ξ ζ := Subtype.ext (map_add (picardAddEquiv gK hsq T) ξ.1 ζ.1)

theorem degreeZeroAddEquiv_map {T T' : BigFppfOver B (Spec (.of K)) hK} (g : T' ⟶ T)
    (ξ : degreeZeroAddSubgroup B hXK hK fK hdimK T) :
    degreeZeroAddEquiv gK hsq hdim hdimK T' (degreeZeroMap B hXK hK fK hdimK g ξ) =
      degreeZeroMap B hX hk f hdim ((restrictSite B hk hK).map g)
        (degreeZeroAddEquiv gK hsq hdim hdimK T ξ) :=
  Subtype.ext (picardAddEquiv_map gK hsq g ξ.1)

theorem degreeZeroAddEquiv_symm_map {T T' : BigFppfOver B (Spec (.of K)) hK} (g : T' ⟶ T)
    (ζ : degreeZeroAddSubgroup B hX hk f hdim ((restrictSite B hk hK).obj T)) :
    (degreeZeroAddEquiv gK hsq hdim hdimK T').symm
        (degreeZeroMap B hX hk f hdim ((restrictSite B hk hK).map g) ζ) =
      degreeZeroMap B hXK hK fK hdimK g ((degreeZeroAddEquiv gK hsq hdim hdimK T).symm ζ) := by
  apply (degreeZeroAddEquiv gK hsq hdim hdimK T').injective
  rw [AddEquiv.apply_symm_apply, degreeZeroAddEquiv_map, AddEquiv.apply_symm_apply]

/-- The comparison of the identity `X_K ×_K T`, regarded as a `k`-scheme: the object
`F (L T)` of `Over (Spec k)` is `(Over.map ι).obj (L T)`. -/
def toOverRestrictIso (T : BigFppfOver B (Spec (.of K)) hK) :
    (BigFppfOver.toOver B (Spec (.of k)) hk).obj ((restrictSite B hk hK).obj T) ≅
      (Over.map (specMap k K)).obj ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T) :=
  Over.isoMk (Iso.refl _) (by simp [siteMap])

omit [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)] in
theorem toOverRestrictIso_hom_left (T : BigFppfOver B (Spec (.of K)) hK) :
    (toOverRestrictIso (hk := hk) T).hom.left = 𝟙 _ := rfl

omit [IsProper (B.inclusion.map f)] [IsProper (B.inclusion.map fK)] in
theorem toOverRestrictIso_naturality {T T' : BigFppfOver B (Spec (.of K)) hK} (g : T' ⟶ T) :
    (toOverRestrictIso (hk := hk) T').hom ≫
        (Over.map (specMap k K)).map ((BigFppfOver.toOver B (Spec (.of K)) hK).map g) =
      (BigFppfOver.toOver B (Spec (.of k)) hk).map ((restrictSite B hk hK).map g) ≫
        (toOverRestrictIso (hk := hk) T).hom := by
  ext1
  simp [toOverRestrictIso_hom_left]

/-- The identification `Hom_K(T, G_K) ≃* Pic⁰_{X_K/K}(T)` for the base change `G_K` of a Jacobian
`G` of `X`: `Hom_K(T, G_K) = Hom_k(T, G) ≃* Pic⁰_{X/k}(T) ≃* Pic⁰_{X_K/K}(T)`. -/
def baseChangeHomMulEquiv {G : Grp (Over (Spec (.of k)))}
    (e : IsJacobianOf B hX hk f hdim G) (T : BigFppfOver B (Spec (.of K)) hK) :
    ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T ⟶
        ((AlgebraicGeometry.GroupScheme.baseChange (specMap k K)).obj G).X) ≃*
      (degreeZeroGrpFunctor B hXK hK fK hdimK).obj (op T) :=
  (AlgebraicGeometry.GroupScheme.pointsMulEquiv (specMap k K) G.X
      ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T)).trans
    ((Stacks.PicardFunctor.homMulEquivOfIso (toOverRestrictIso (hk := hk) T)).trans
      ((e.homMulEquiv ((restrictSite B hk hK).obj T)).trans
        (degreeZeroAddEquiv gK hsq hdim hdimK T).symm.toMultiplicative))

theorem baseChangeHomMulEquiv_apply {G : Grp (Over (Spec (.of k)))}
    (e : IsJacobianOf B hX hk f hdim G) (T : BigFppfOver B (Spec (.of K)) hK)
    (a : (BigFppfOver.toOver B (Spec (.of K)) hK).obj T ⟶
        ((AlgebraicGeometry.GroupScheme.baseChange (specMap k K)).obj G).X) :
    baseChangeHomMulEquiv gK hsq hdim hdimK e T a =
      (degreeZeroAddEquiv gK hsq hdim hdimK T).symm.toMultiplicative
        (e.homMulEquiv ((restrictSite B hk hK).obj T)
          ((toOverRestrictIso (hk := hk) T).hom ≫
            AlgebraicGeometry.GroupScheme.pointsMulEquiv (specMap k K) G.X
              ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T) a)) :=
  rfl

theorem baseChangeHomMulEquiv_naturality {G : Grp (Over (Spec (.of k)))}
    (e : IsJacobianOf B hX hk f hdim G) {T T' : BigFppfOver B (Spec (.of K)) hK} (g : T' ⟶ T)
    (a : (BigFppfOver.toOver B (Spec (.of K)) hK).obj T ⟶
        ((AlgebraicGeometry.GroupScheme.baseChange (specMap k K)).obj G).X) :
    baseChangeHomMulEquiv gK hsq hdim hdimK e T'
        ((BigFppfOver.toOver B (Spec (.of K)) hK).map g ≫ a) =
      (degreeZeroGrpFunctor B hXK hK fK hdimK).map g.op
        (baseChangeHomMulEquiv gK hsq hdim hdimK e T a) := by
  have h1 : AlgebraicGeometry.GroupScheme.pointsMulEquiv (specMap k K) G.X
      ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T')
      ((BigFppfOver.toOver B (Spec (.of K)) hK).map g ≫ a) =
      (Over.map (specMap k K)).map ((BigFppfOver.toOver B (Spec (.of K)) hK).map g) ≫
        AlgebraicGeometry.GroupScheme.pointsMulEquiv (specMap k K) G.X
          ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T) a := by
    ext1
    rw [AlgebraicGeometry.GroupScheme.pointsMulEquiv_apply_left]
    erw [Over.comp_left, Over.comp_left]
    simp only [Category.assoc, Over.map_map_left]
    congr 1
  have h2 := e.homMulEquiv_naturality ((restrictSite B hk hK).map g)
    ((toOverRestrictIso (hk := hk) T).hom ≫
      AlgebraicGeometry.GroupScheme.pointsMulEquiv (specMap k K) G.X
        ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T) a)
  have h3 : (toOverRestrictIso (hk := hk) T').hom ≫
      ((Over.map (specMap k K)).map ((BigFppfOver.toOver B (Spec (.of K)) hK).map g) ≫
        AlgebraicGeometry.GroupScheme.pointsMulEquiv (specMap k K) G.X
          ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T) a) =
      (BigFppfOver.toOver B (Spec (.of k)) hk).map ((restrictSite B hk hK).map g) ≫
        ((toOverRestrictIso (hk := hk) T).hom ≫
          AlgebraicGeometry.GroupScheme.pointsMulEquiv (specMap k K) G.X
            ((BigFppfOver.toOver B (Spec (.of K)) hK).obj T) a) := by
    rw [← Category.assoc, toOverRestrictIso_naturality, Category.assoc]
  have h13 := (congrArg (fun m => (toOverRestrictIso (hk := hk) T').hom ≫ m) h1).trans h3
  refine (baseChangeHomMulEquiv_apply gK hsq hdim hdimK e T' _).trans ?_
  refine (congrArg (fun m => (degreeZeroAddEquiv gK hsq hdim hdimK T').symm.toMultiplicative
    (e.homMulEquiv ((restrictSite B hk hK).obj T') m)) h13).trans ?_
  refine (congrArg (degreeZeroAddEquiv gK hsq hdim hdimK T').symm.toMultiplicative h2).trans ?_
  refine Eq.trans ?_ (congrArg ((degreeZeroGrpFunctor B hXK hK fK hdimK).map g.op)
    (baseChangeHomMulEquiv_apply gK hsq hdim hdimK e T a).symm)
  apply Multiplicative.toAdd.injective
  exact Subtype.ext (congrArg Subtype.val
    (degreeZeroAddEquiv_symm_map gK hsq hdim hdimK g _))

/-- **Base change of a Jacobian.** Let `K/k` be a field extension, `X_K = X ×_k K` a base change of
the curve in the site, and `G` a Jacobian of `X` over `k`. Then the base change `G_K` of the group
scheme `G` is a Jacobian of `X_K` over `K`: it represents the relative Picard
sheaf `Pic⁰_{X_K/K}`, because `Pic_{X_K/K}` is the restriction of `Pic_{X/k}`
(`picardAddEquiv`) and `Hom_K(T, G_K) = Hom_k(T, G)`. -/
def isJacobianOf_baseChange {G : Grp (Over (Spec (.of k)))}
    (e : IsJacobianOf B hX hk f hdim G) :
    IsJacobianOf B hXK hK fK hdimK
      ((AlgebraicGeometry.GroupScheme.baseChange (specMap k K)).obj G) where
  homMulEquiv T := baseChangeHomMulEquiv gK hsq hdim hdimK e T
  homMulEquiv_naturality g a := baseChangeHomMulEquiv_naturality gK hsq hdim hdimK e g a
  isAbelianVariety := by
    have := e.isAbelianVariety
    exact AlgebraicGeometry.isAbelianVariety_pullbackObj (K := K) G.X

end GroupBaseChange

end BaseChange

end Jacobian

end ArithmeticOfJacobiPolynomials

end
