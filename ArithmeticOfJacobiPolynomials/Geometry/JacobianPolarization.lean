/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianPolarization
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.AbelJacobi

/-!
# The Abel–Jacobi map and the canonical polarization correspondence

The Abel–Jacobi map is characterized by the diagonal family minus the constant
point family through the relative Picard representation. Its uniqueness is proved.
The canonical polarization correspondence is the negative of the normalized
diagonal class, as in Milne, Jacobian Varieties, Summary 6.11. These are geometric
characterizations.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
  Opposite Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

namespace ArithmeticOfJacobiPolynomials.Jacobian

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}}
  (hX : B.Contains X) (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  {hdim : topologicalKrullDim X ≤ 1} {J : Grp (Over (Spec (.of k)))}
  (hJ : IsJacobianOf B hX hk f hdim J)

/-- A morphism is the Abel–Jacobi map precisely when the relative Picard
representation sends it to the class `O(Δ - {σ} × X)`. -/
def IsAbelJacobi (a : curveOver B hX hk f ⟶ J.X) : Prop :=
  (Multiplicative.toAdd (hJ.homMulEquiv (curveObj B hX hk f) a)).1 =
    toPicardFunctorHom B hX hk f (curveObj B hX hk f)
      (abelJacobiClass B hX hk f σ hσ)

omit [GeometricallyIrreducible (B.inclusion.map f)] in
/-- The relative Picard universal property determines the Abel–Jacobi map uniquely. -/
theorem IsAbelJacobi.unique {a b : curveOver B hX hk f ⟶ J.X}
    (ha : IsAbelJacobi B hX hk f σ hσ hJ a)
    (hb : IsAbelJacobi B hX hk f σ hσ hJ b) : a = b := by
  apply (hJ.homMulEquiv (curveObj B hX hk f)).injective
  apply Multiplicative.toAdd.injective
  exact Subtype.ext (ha.trans hb.symm)

/-- The normalized diagonal class `O(Δ - {σ} × X - X × {σ})`, using the
library's effective Cartier families and the interchange of the factors. -/
def normalizedDiagonalClass :
    Stacks.Picard.ofScheme (curveOver B hX hk f ⊗ curveOver B hX hk f).left :=
  (show Stacks.Picard.ofScheme (curveOver B hX hk f ⊗ curveOver B hX hk f).left from
    abelJacobiClass B hX hk f σ hσ) -
      Stacks.Picard.schemePullbackClass
        (β_ (curveOver B hX hk f) (curveOver B hX hk f)).hom.left
        (constantFamily B hX hk f σ hσ).picardClass

variable {D : Over (Spec (.of k))} [GrpObj D]

/-- The pullback of a Poincaré class by `(aj, φ ∘ aj)` is the negative
normalized diagonal correspondence. Together with the ample principal condition,
this is the canonical Jacobian polarization characterization of Milne JV 6.11. -/
def IsCanonicalCorrespondence
    (a : curveOver B hX hk f ⟶ J.X)
    (P : Stacks.Picard.ofScheme (J.X ⊗ D).left) (φ : J.X ⟶ D) : Prop :=
  Stacks.Picard.schemePullbackClass
      (lift (fst (curveOver B hX hk f) (curveOver B hX hk f) ≫ a)
        (snd (curveOver B hX hk f) (curveOver B hX hk f) ≫ a ≫ φ)).left P =
    -normalizedDiagonalClass B hX hk f σ hσ

omit [GeometricallyIrreducible (B.inclusion.map f)] [GrpObj D] in
/-- The correspondence condition is independent of the selected witness of the
Abel–Jacobi universal property. -/
theorem IsCanonicalCorrespondence.iff_of_isAbelJacobi
    {a b : curveOver B hX hk f ⟶ J.X}
    (ha : IsAbelJacobi B hX hk f σ hσ hJ a)
    (hb : IsAbelJacobi B hX hk f σ hσ hJ b)
    (P : Stacks.Picard.ofScheme (J.X ⊗ D).left) (φ : J.X ⟶ D) :
    IsCanonicalCorrespondence B hX hk f σ hσ a P φ ↔
      IsCanonicalCorrespondence B hX hk f σ hσ b P φ := by
  rw [ha.unique B hX hk f σ hσ hJ hb]

end ArithmeticOfJacobiPolynomials.Jacobian

namespace ArithmeticOfJacobiPolynomials.Jacobian

variable {k : Type u} [Field k]

/-- Pull the original Poincaré class back along the two geometric Abel–Jacobi
maps. The second map is followed by the original polarization over `k`. -/
def geometricCorrespondenceMap
    (C A D : Over (Spec (.of k))) (φ : A ⟶ D)
    (Ω : Type u) [Field Ω] [Algebra k Ω]
    (a : GroupScheme.baseChange Ω C ⟶ GroupScheme.baseChange Ω A) :
    (GroupScheme.baseChange Ω C ⊗ GroupScheme.baseChange Ω C).left ⟶ (A ⊗ D).left :=
  let F := Over.map (GroupScheme.specMapAlgebra (k := k) Ω)
  let ε := (Over.mapPullbackAdj (GroupScheme.specMapAlgebra (k := k) Ω)).counit.app A
  (lift (F.map (fst _ _ ≫ a) ≫ ε) (F.map (snd _ _ ≫ a) ≫ ε ≫ φ)).left

/-- The canonical principal polarization over an arbitrary field, characterized
geometrically by the negative normalized diagonal correspondence. Every geometric
base change is the degree-zero Picard representer, and the condition is
required for every base point and every site presentation. The definition does not
require a rational point on the original curve. -/
structure IsCanonicalPrincipalPolarization
    (C : Over (Spec (.of k))) (J : Grp (Over (Spec (.of k))))
    (D : Over (Spec (.of k))) [GrpObj D]
    (P : Stacks.Picard.ofScheme (J.X ⊗ D).left) (φ : J.X ⟶ D) [IsMonHom φ] : Prop where
  poincare : Nonempty (AbelianDuality.IsPoincarePair J.X D P)
  principal : AbelianDuality.IsPrincipalPolarization J.X D P φ
  correspondence : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (B : BigFppfSite.{u})
    (hC : B.Contains (GroupScheme.baseChange Ω C).left)
    (hΩ : B.Contains (Spec (.of Ω))),
    let g : B.obj hC ⟶ B.obj hΩ := ObjectProperty.homMk (GroupScheme.baseChange Ω C).hom
    ∀ [IsCurve Ω (B.inclusion.map g)] [GeometricallyIrreducible (B.inclusion.map g)]
    [Smooth (B.inclusion.map g)] [IsProper (B.inclusion.map g)]
    [IsProjectiveVariety Ω (B.inclusion.map g)]
    (σ : Spec (.of Ω) ⟶ (GroupScheme.baseChange Ω C).left)
    (hσ : σ ≫ B.inclusion.map g = 𝟙 _),
      let JΩ := (AlgebraicGeometry.GroupScheme.baseChange
        (GroupScheme.specMapAlgebra (k := k) Ω)).obj J
      ∃ hJΩ : IsJacobianOf B hC hΩ g
        (IsCurve.topologicalKrullDim_eq_one (k := Ω) (f := B.inclusion.map g)).le JΩ,
        ∃ a : curveOver B hC hΩ g ⟶ JΩ.X,
          IsAbelJacobi B hC hΩ g σ hσ hJΩ a ∧
            Stacks.Picard.schemePullbackClass
              (geometricCorrespondenceMap C J.X D φ Ω a) P =
              -normalizedDiagonalClass B hC hΩ g σ hσ

end ArithmeticOfJacobiPolynomials.Jacobian
