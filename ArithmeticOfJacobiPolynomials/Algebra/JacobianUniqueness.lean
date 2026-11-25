/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Basic
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.BigSiteRestriction

/-!
# Uniqueness of the Jacobian as a group scheme (Yoneda on the big fppf site)

Let `B` be a big fppf site, `S` a scheme of the site, and `L = BigFppfOver.toOver B S hS` the
fully faithful inclusion of the `S`-schemes of the site into all `S`-schemes. Two group objects
`G₁ G₂` of `Over S`, whose underlying schemes lie in the site, are isomorphic as group objects as
soon as the functors `T ↦ Hom_S(L T, Gᵢ)` of test schemes in the site are naturally isomorphic as
presheaves of **groups** (`exists_grpIso_of_naturalMulEquiv`). This is Yoneda, restricted to the
site: the representing object is recovered from its value on itself.

## Main results

* `ArithmeticOfJacobiPolynomials.Jacobian.exists_grpIso_of_naturalMulEquiv`: the generic statement,
with the
  isomorphism characterised by `a ≫ e.hom.hom.hom = φ T a`.
* `ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf.contains_left`: the representing scheme of an
  `IsJacobianOf` lies in the site (it is of finite type over `k`).
* `ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf.exists_grpIso`: **uniqueness of the Jacobian
as a group
  scheme**: two `IsJacobianOf` representers of the same data are isomorphic in
  `Grp (Over (Spec k))`, by an isomorphism compatible with the two representations.
* `ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf.grpIso_unique`: that isomorphism is unique.

No existence of a Jacobian and no rational point is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials

namespace Jacobian

section Yoneda

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

local notation "𝓛" => BigFppfOver.toOver B S hS

/-- A scheme `G` over `S` lying below the cutoff of `B`, viewed as an `S`-scheme of the site. -/
def siteObj (G : Over S) (hG : B.Contains G.left) : BigFppfOver B S hS :=
  Over.mk (Y := B.obj hG) (B.inclusion.preimage G.hom)

/-- The `S`-scheme of the site attached to `G` is `G`. -/
def siteObjIso (G : Over S) (hG : B.Contains G.left) :
    (BigFppfOver.toOver B S hS).obj (siteObj B hS G hG) ≅ G :=
  Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans
      (B.inclusion.map_preimage (X := B.obj hG) (Y := B.obj hS) G.hom).symm)

/-- The terminal `S`-scheme of the site. -/
def unitSite : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The terminal `S`-scheme of the site is the unit object of `Over S`. -/
def unitSiteIso : (BigFppfOver.toOver B S hS).obj (unitSite B hS) ≅ 𝟙_ (Over S) :=
  IsTerminal.uniqueUpToIso (Over.mkIdTerminal (X := S)) isTerminalTensorUnit

/-- **Yoneda for group objects, restricted to the site.** Let `G₁ G₂` be group objects of `Over S`
below the cutoff of `B`, and `φ T : Hom_S(T, G₁) ≃* Hom_S(T, G₂)` a family of group isomorphisms,
indexed by the `S`-schemes `T` of the site and natural in `T`. Then there is an isomorphism
`e : G₁ ≅ G₂` of group objects with `a ≫ e.hom.hom.hom = φ T a`. -/
theorem exists_grpIso_of_naturalMulEquiv (G₁ G₂ : Grp (Over S))
    (h₁ : B.Contains G₁.X.left) (h₂ : B.Contains G₂.X.left)
    (φ : ∀ T : BigFppfOver B S hS,
      ((𝓛).obj T ⟶ G₁.X) ≃* ((𝓛).obj T ⟶ G₂.X))
    (hφ : ∀ {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
      (a : (𝓛).obj T ⟶ G₁.X),
      φ T' ((𝓛).map g ≫ a) = (𝓛).map g ≫ φ T a) :
    ∃ e : G₁ ≅ G₂, ∀ (T : BigFppfOver B S hS) (a : (𝓛).obj T ⟶ G₁.X),
      a ≫ e.hom.hom.hom = φ T a := by
  have hψ : ∀ {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (a : (𝓛).obj T ⟶ G₂.X),
      (φ T').symm ((𝓛).map g ≫ a) = (𝓛).map g ≫ (φ T).symm a := fun {T T'} g a =>
    (φ T').injective (by rw [MulEquiv.apply_symm_apply, hφ, MulEquiv.apply_symm_apply])
  -- the representatives of `G₁` and `G₂` in the site
  let T₁ := siteObj B hS G₁.X h₁
  let T₂ := siteObj B hS G₂.X h₂
  let t₁ : (𝓛).obj T₁ ≅ G₁.X := siteObjIso B hS G₁.X h₁
  let t₂ : (𝓛).obj T₂ ≅ G₂.X := siteObjIso B hS G₂.X h₂
  let u : G₁.X ⟶ G₂.X := t₁.inv ≫ φ T₁ t₁.hom
  let v : G₂.X ⟶ G₁.X := t₂.inv ≫ (φ T₂).symm t₂.hom
  have hu : ∀ (T : BigFppfOver B S hS) (x : (𝓛).obj T ⟶ G₁.X), x ≫ u = φ T x := by
    intro T x
    obtain ⟨y, hy⟩ := (BigFppfOver.fullyFaithfulToOver B S hS).map_surjective (x ≫ t₁.inv)
    have hx : x = (𝓛).map y ≫ t₁.hom := by
      have : (𝓛).map y = x ≫ t₁.inv := hy
      rw [this]; simp
    rw [hx, hφ y t₁.hom]
    simp [u]
  have hv : ∀ (T : BigFppfOver B S hS) (x : (𝓛).obj T ⟶ G₂.X), x ≫ v = (φ T).symm x := by
    intro T x
    obtain ⟨y, hy⟩ := (BigFppfOver.fullyFaithfulToOver B S hS).map_surjective (x ≫ t₂.inv)
    have hx : x = (𝓛).map y ≫ t₂.hom := by
      have : (𝓛).map y = x ≫ t₂.inv := hy
      rw [this]; simp
    rw [hx, hψ y t₂.hom]
    simp [v]
  have huv : u ≫ v = 𝟙 _ := by
    refine (cancel_epi t₁.hom).1 ?_
    rw [← Category.assoc, hu, hv, MulEquiv.symm_apply_apply, Category.comp_id]
  have hvu : v ≫ u = 𝟙 _ := by
    refine (cancel_epi t₂.hom).1 ?_
    rw [← Category.assoc, hv, hu, MulEquiv.apply_symm_apply, Category.comp_id]
  let e : G₁.X ≅ G₂.X := ⟨u, v, huv, hvu⟩
  -- unit
  let U := unitSite B hS
  let tU : (𝓛).obj U ≅ 𝟙_ (Over S) := unitSiteIso B hS
  have hone : η[G₁.X] ≫ u = η[G₂.X] := by
    refine (cancel_epi tU.hom).1 ?_
    have h1 : tU.hom ≫ η[G₁.X] = (1 : (𝓛).obj U ⟶ G₁.X) := by
      rw [Hom.one_def]; congr 1
    have h2 : tU.hom ≫ η[G₂.X] = (1 : (𝓛).obj U ⟶ G₂.X) := by
      rw [Hom.one_def]; congr 1
    rw [← Category.assoc, h1, h2]
    exact (hu U 1).trans (map_one (φ U))
  -- multiplication
  have hmul : μ[G₁.X] ≫ u = (u ⊗ₘ u) ≫ μ[G₂.X] := by
    have hP : B.Contains (G₁.X ⊗ G₁.X).left := Scheme.size_pullback_lt _ _ h₁ h₁
    let TP := siteObj B hS (G₁.X ⊗ G₁.X) hP
    let tP : (𝓛).obj TP ≅ G₁.X ⊗ G₁.X := siteObjIso B hS (G₁.X ⊗ G₁.X) hP
    refine (cancel_epi tP.hom).1 ?_
    set x₁ : (𝓛).obj TP ⟶ G₁.X := tP.hom ≫ fst _ _
    set x₂ : (𝓛).obj TP ⟶ G₁.X := tP.hom ≫ snd _ _
    have hlift : lift x₁ x₂ = tP.hom := by simp [x₁, x₂]
    have h1 : tP.hom ≫ μ[G₁.X] ≫ u = φ TP (x₁ * x₂) := by
      rw [← hu, Hom.mul_def, hlift]
      simp
    have h2 : φ TP (x₁ * x₂) = φ TP x₁ * φ TP x₂ := map_mul _ _ _
    have h3 : φ TP x₁ * φ TP x₂ = lift (x₁ ≫ u) (x₂ ≫ u) ≫ μ[G₂.X] := by
      rw [← hu, ← hu, Hom.mul_def]
    have h4 : lift (x₁ ≫ u) (x₂ ≫ u) = tP.hom ≫ (u ⊗ₘ u) := by
      apply hom_ext <;> simp [x₁, x₂]
    rw [h1, h2, h3, h4, Category.assoc]
  refine ⟨Grp.mkIso e hone hmul, fun T a => ?_⟩
  simpa [Grp.mkIso, e] using hu T a

end Yoneda

section IsJacobianOf

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1)

/-- **The representing scheme of a Jacobian lies in the site**: it is an abelian variety, hence
of finite type over `k`, hence below the cutoff of any site containing `Spec k`. -/
theorem IsJacobianOf.contains_left {G : Grp (Over (Spec (.of k)))}
    (e : IsJacobianOf B hX hk f hdim G) : B.Contains G.X.left := by
  have := e.isAbelianVariety
  exact (Scheme.size_le_of_locallyOfFiniteType G.X.hom).trans_lt hk

/-- **Uniqueness of the Jacobian as a group scheme.** Two group schemes representing the same
`Pic⁰_{X/k}` are isomorphic as group objects of `Over (Spec k)`, by an isomorphism that commutes
with the two representations: `a ≫ e.hom.hom.hom` corresponds, under `e₂`, to the element of
`Pic⁰_{X/k}(T)` that `e₁` attaches to `a`. -/
theorem IsJacobianOf.exists_grpIso {G₁ G₂ : Grp (Over (Spec (.of k)))}
    (e₁ : IsJacobianOf B hX hk f hdim G₁) (e₂ : IsJacobianOf B hX hk f hdim G₂) :
    ∃ e : G₁ ≅ G₂, ∀ (T : BigFppfOver B (Spec (.of k)) hk)
      (a : (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ G₁.X),
      e₂.homMulEquiv T (a ≫ e.hom.hom.hom) = e₁.homMulEquiv T a := by
  obtain ⟨e, he⟩ := exists_grpIso_of_naturalMulEquiv B hk G₁ G₂
    (e₁.contains_left B hX hk f hdim) (e₂.contains_left B hX hk f hdim)
    (fun T => (e₁.homMulEquiv T).trans (e₂.homMulEquiv T).symm)
    (fun {T T'} g a => by
      refine (e₂.homMulEquiv T').injective ?_
      change e₂.homMulEquiv T' ((e₂.homMulEquiv T').symm (e₁.homMulEquiv T' _)) = _
      rw [MulEquiv.apply_symm_apply, e₁.homMulEquiv_naturality, e₂.homMulEquiv_naturality]
      simp)
  refine ⟨e, fun T a => ?_⟩
  rw [he]
  exact (e₂.homMulEquiv T).apply_symm_apply _

/-- The isomorphism of `ArithmeticOfJacobiPolynomials.Jacobian.IsJacobianOf.exists_grpIso` is the
unique one
compatible with the two representations. -/
theorem IsJacobianOf.grpIso_unique {G₁ G₂ : Grp (Over (Spec (.of k)))}
    (e₁ : IsJacobianOf B hX hk f hdim G₁) (e₂ : IsJacobianOf B hX hk f hdim G₂)
    (ε ε' : G₁ ≅ G₂)
    (hε : ∀ (T : BigFppfOver B (Spec (.of k)) hk)
      (a : (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ G₁.X),
      e₂.homMulEquiv T (a ≫ ε.hom.hom.hom) = e₁.homMulEquiv T a)
    (hε' : ∀ (T : BigFppfOver B (Spec (.of k)) hk)
      (a : (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ G₁.X),
      e₂.homMulEquiv T (a ≫ ε'.hom.hom.hom) = e₁.homMulEquiv T a) :
    ε = ε' := by
  let T₁ := siteObj B hk G₁.X (e₁.contains_left B hX hk f hdim)
  let t₁ := siteObjIso B hk G₁.X (e₁.contains_left B hX hk f hdim)
  have h : t₁.hom ≫ ε.hom.hom.hom = t₁.hom ≫ ε'.hom.hom.hom :=
    (e₂.homMulEquiv T₁).injective ((hε T₁ t₁.hom).trans (hε' T₁ t₁.hom).symm)
  have h' : ε.hom.hom.hom = ε'.hom.hom.hom := (cancel_epi t₁.hom).1 h
  ext1
  ext1
  exact h'

end IsJacobianOf

end Jacobian

end ArithmeticOfJacobiPolynomials

end
