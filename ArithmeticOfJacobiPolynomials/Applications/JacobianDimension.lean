/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.JacobianBaseChange
public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.AlgClosed
public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Hyperelliptic
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange

/-!
# The dimension of an arbitrary Jacobian of a curve

`dim J = genus X` for **any** group scheme `J` representing `Pic⁰_{X/k}` as an abelian variety
(`ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf`), over **any** field `k`. This is the first
assertion of
Corollary 6.6 (`dim J_f = ⌊(d - 1)/2⌋`), in the form which uses neither a rational point nor a
specific construction of `J`.

The proof is the manuscript's own transfer:

1. over an algebraically closed field `K`, Stacks' `P⁰ = Pic⁰_{X/K}` is a Jacobian
   (`ArithmeticOfJacobiPolynomials.Jacobian.nonempty_isJacobianOf_degreeZeroOpenSubgroupScheme`) of
   dimension
   `genus X` (`Stacks.PicardFunctor.isAbelianVariety_degreeZeroOpenSubgroupScheme`); any other
   Jacobian is isomorphic to it as a group scheme by Yoneda
   (`ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf.exists_grpIso`), hence has the same
   dimension
   (`abelianVarietyDimension_eq_genus_of_isAlgClosed`);
2. over an arbitrary field `k`, the base change `J_K` of a Jacobian of `X` along `K/k` is a
   Jacobian of `X_K` (`ArithmeticOfJacobiPolynomials.Jacobian.BaseChange.isJacobianOf_baseChange`),
   since
   `Pic_{X_K/K}` is the restriction of `Pic_{X/k}`; the dimension of `J_K` is that of `J`
   (`abelianVarietyDimension_pullback`), and the genus of `X_K` is that of `X`
   (`AlgebraicGeometry.genus_baseChange`).

## Main results

* `ArithmeticOfJacobiPolynomials.Jacobian.abelianVarietyDimension_eq_genus_of_isAlgClosed`
* `ArithmeticOfJacobiPolynomials.Jacobian.abelianVarietyDimension_eq_genus_of_isJacobianOf`: the
general bridge,
  with the base-changed curve, a field extension `K/k` with `K` algebraically closed, and the
  cartesian square as input data in a big fppf site.
* `ArithmeticOfJacobiPolynomials.Jacobian.abelianVarietyDimension_hyperelliptic`: the
specialization to the
  smooth projective hyperelliptic model: `dim J = ⌊(deg f - 1)/2⌋`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Jacobian

section Dimension

variable {k : Type u} [Field k]

/-- The dimension of an abelian variety only depends on its underlying scheme. -/
theorem abelianVarietyDimension_congr {A A' : Over (Spec (.of k))} (e : A ≅ A') :
    Stacks.Groupoids.abelianVarietyDimension A = Stacks.Groupoids.abelianVarietyDimension A' := by
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have h : topologicalKrullDim A.left = topologicalKrullDim A'.left :=
    IsHomeomorph.topologicalKrullDim_eq _ e.hom.left.homeomorph.isHomeomorph
  unfold Stacks.Groupoids.abelianVarietyDimension
  rw [h]

/-- The dimension of an abelian variety is unchanged by a field extension. -/
theorem abelianVarietyDimension_pullback {K : Type u} [Field K] [Algebra k K]
    (A : Over (Spec (.of k))) [LocallyOfFiniteType A.hom] :
    Stacks.Groupoids.abelianVarietyDimension
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) =
      Stacks.Groupoids.abelianVarietyDimension A := by
  have : Subsingleton (Spec (.of k)) := inferInstance
  have : Subsingleton (Spec (.of K)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun y => ⟨(default : Spec (.of K)), Subsingleton.elim _ _⟩⟩
  have h : topologicalKrullDim
      (pullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) =
      topologicalKrullDim A.left :=
    topologicalKrullDim_eq_of_isPullback_of_subsingleton (IsPullback.of_hasPullback _ _)
  unfold Stacks.Groupoids.abelianVarietyDimension
  change ((topologicalKrullDim (pullback A.hom _ : Scheme.{u})).unbotD 0).toNat = _
  rw [h]

end Dimension

section AlgClosed

attribute [local instance] bigFppfOverCartesianMonoidal toOverMonoidal

variable (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (k : Type u) [Field k]
  [IsAlgClosed k] {hk : B.Contains (Spec (.of k))} (g : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
  [Smooth (B.inclusion.map g)]

/-- A group-object isomorphism is an isomorphism of the underlying objects. -/
def grpIsoToOverIso {S : Scheme.{u}} {G₁ G₂ : Grp (Over S)} (e : G₁ ≅ G₂) : G₁.X ≅ G₂.X :=
  ⟨e.hom.hom.hom, e.inv.hom.hom, congrArg (fun φ => φ.hom.hom) e.hom_inv_id,
    congrArg (fun φ => φ.hom.hom) e.inv_hom_id⟩

/-- **Every Jacobian over an algebraically closed field has dimension the genus.** Any group scheme
`G` representing `Pic⁰_{X/k}` as an abelian variety is isomorphic, as a group scheme and by
Yoneda (`IsJacobianOf.exists_grpIso`), to Stacks' `Pic⁰` of
`ArithmeticOfJacobiPolynomials.Jacobian.exists_isJacobianOf_of_isAlgClosed`, so `dim G = genus X`.
-/
theorem abelianVarietyDimension_eq_genus_of_isAlgClosed {G : Grp (Over (Spec (.of k)))}
    (e : IsJacobianOf B hX hk g (topologicalKrullDim_le_one_of_curve B hX k g) G) :
    Stacks.Groupoids.abelianVarietyDimension G.X = genus (B.inclusion.map g) := by
  obtain ⟨G₀, ⟨e₀⟩, hdim⟩ := exists_isJacobianOf_of_isAlgClosed B hX k g
  obtain ⟨ε, -⟩ := e.exists_grpIso B hX hk g _ e₀
  rw [abelianVarietyDimension_congr (grpIsoToOverIso ε), hdim]

end AlgClosed

section General

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] (B : BigFppfSite.{u})
  {X : Scheme.{u}} (hX : B.Contains X) (hk : B.Contains (Spec (.of k)))
  (hK : B.Contains (Spec (.of K))) (f : B.obj hX ⟶ B.obj hk)
  {XK : Scheme.{u}} (hXK : B.Contains XK) (fK : B.obj hXK ⟶ B.obj hK)
  (gK : XK ⟶ X)
  (hsq : IsPullback gK (B.inclusion.map fK) (B.inclusion.map f)
    (B.inclusion.map (BaseChange.siteMap B hk hK)))
  [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1)

attribute [local instance] bigFppfOverCartesianMonoidal toOverMonoidal

include hsq in
/-- **The dimension of an arbitrary Jacobian over an arbitrary field** (first assertion of
Corollary 6.6). Let `G` be any group scheme over `k` representing `Pic⁰_{X/k}` as an abelian
variety, and `K/k` an extension with `K` algebraically closed, `X_K = X ×_k K` the base-changed
curve, assumed (as it is for a smooth projective geometrically integral curve) a smooth
projective curve over `K`. Then `dim G = genus X`: the base change `G_K` is a Jacobian of `X_K`
(`BaseChange.isJacobianOf_baseChange`), hence has dimension `genus X_K = genus X`. -/
theorem abelianVarietyDimension_eq_genus_of_isJacobianOf
    [IsCurve K (B.inclusion.map fK)] [IsProjectiveVariety K (B.inclusion.map fK)]
    [Smooth (B.inclusion.map fK)] {G : Grp (Over (Spec (.of k)))}
    (e : IsJacobianOf B hX hk f hdim G) :
    Stacks.Groupoids.abelianVarietyDimension G.X = genus (B.inclusion.map f) := by
  have hdimK := topologicalKrullDim_le_one_of_curve B hXK K fK
  have := e.isAbelianVariety
  have eK := BaseChange.isJacobianOf_baseChange gK hsq hdim hdimK e
  have h1 := abelianVarietyDimension_eq_genus_of_isAlgClosed B hXK K fK eK
  have h2 : Stacks.Groupoids.abelianVarietyDimension
      ((AlgebraicGeometry.GroupScheme.baseChange (BaseChange.specMap k K)).obj G).X =
      Stacks.Groupoids.abelianVarietyDimension G.X :=
    abelianVarietyDimension_pullback (K := K) G.X
  rw [← h2, h1]
  exact genus_baseChange k K gK (B.inclusion.map fK) (B.inclusion.map f) hsq

end General

section Hyperelliptic

open Polynomial ArithmeticOfJacobiPolynomials.Hyperelliptic

attribute [local instance] bigFppfOverCartesianMonoidal toOverMonoidal

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {f : k[X]}

/-- **The dimension of an arbitrary Jacobian of the hyperelliptic curve** (first assertion of
Corollary 6.6): for `f ∈ k[x]` separable of degree `d ≥ 1` over a field `k` with `2 ≠ 0`, and any
group scheme `G` over `k` which represents `Pic⁰_{X_f/k}` as an abelian variety (in a big fppf
site containing the model over `k`, over a chosen algebraically closed `K ⊇ k`, and the
structure morphisms), `dim G = ⌊(d - 1)/2⌋`. -/
theorem abelianVarietyDimension_hyperelliptic (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (B : BigFppfSite.{u})
    (hX : B.Contains (projectiveModel f)) (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K)))
    (hXK : B.Contains (projectiveModel (f.map (algebraMap k K))))
    (g : B.obj hX ⟶ B.obj hk) (hg : B.inclusion.map g = toSpecField f)
    [IsProper (B.inclusion.map g)] (gK : B.obj hXK ⟶ B.obj hK)
    (hgK : B.inclusion.map gK = toSpecField (f.map (algebraMap k K)))
    {G : Grp (Over (Spec (.of k)))}
    (e : Jacobian.IsJacobianOf B hX hk g
      (projectiveModel_curve h2 hf hdeg).2.2.2.le G) :
    Stacks.Groupoids.abelianVarietyDimension G.X = (f.natDegree - 1) / 2 := by
  have h2' : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap k K) 2]
    exact (_root_.map_ne_zero _).mpr h2
  have hdeg' : 0 < (f.map (algebraMap k K)).natDegree := by
    rw [natDegree_map]; exact hdeg
  have hsq : IsPullback (baseChangeMap K f) (B.inclusion.map gK) (B.inclusion.map g)
      (B.inclusion.map (Jacobian.BaseChange.siteMap B hk hK)) := by
    rw [hg, hgK]; exact isPullback_baseChangeMap K f
  have : IsCurve K (B.inclusion.map gK) := by
    rw [hgK]; exact isCurve_toSpecField h2' hf.map hdeg'
  have : IsProjectiveVariety K (B.inclusion.map gK) := by
    rw [hgK]; exact isProjectiveVariety_toSpecField h2' hf.map hdeg'
  have : Smooth (B.inclusion.map gK) := by
    rw [hgK]; exact smooth_toSpecField h2' hf.map hdeg'
  have h := abelianVarietyDimension_eq_genus_of_isJacobianOf B hX hk hK g hXK gK
    (baseChangeMap K f) hsq _ e
  rw [h, hg, genus_toSpecField]

end Hyperelliptic

end Jacobian

end ArithmeticOfJacobiPolynomials

end
