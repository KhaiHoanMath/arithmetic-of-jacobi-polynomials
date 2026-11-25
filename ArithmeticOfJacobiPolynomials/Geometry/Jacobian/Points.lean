/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Transport
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.RepresentingGroup
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.ResidueDegree

/-!
# Degree-zero Picard classes are points of every geometric Jacobian

The Stacks comparison `Pic(X) ≃ Pic_{X/k}(Spec k)` preserves the degree.
Restricting it to degree zero and applying the Jacobian's representing property
identifies line-bundle classes with rational points. Over the algebraically closed field `k` the
geometric-fibre `Pic⁰_{X/k}` represented by a Jacobian is the Stacks residue-field subfunctor
(`ArithmeticOfJacobiPolynomials.Jacobian.mem_degreeZeroAddSubgroup_iff_of_isAlgClosed`), whose
degree at `Spec k` is the degree on `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials.Jacobian

variable {k : Type u} [Field k] [IsAlgClosed k] (B : BigFppfSite.{u}) {X : Scheme.{u}}
  (hX : B.Contains X) (hk : B.Contains (Spec (.of k))) (g : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
  [Smooth (B.inclusion.map g)] [IsProper (B.inclusion.map g)]
  (hdim : topologicalKrullDim X ≤ 1)

/-- The Stacks Picard comparison carries degree-zero classes to degree-zero sections. -/
theorem mem_degreeZeroAtBase_iff (c : Stacks.Picard.ofScheme X) :
    ofSchemeAddEquivPicardFunctorOfCurve B hX k g c ∈
        degreeZeroAddSubgroup B hX hk g hdim (terminalTest B hk) ↔
      c ∈ Stacks.Picard.ofSchemeDegreeZero k (B.inclusion.map g) hdim := by
  rw [mem_degreeZeroAddSubgroup_iff_of_isAlgClosed B hX k g hdim,
    mem_degreeZeroSubfunctor_iff_residueDegree B hX k g]
  simp only [residueDegree_ofSchemeAddEquivPicardFunctorOfCurve B hX k g hdim]
  exact ⟨fun h => h (IsLocalRing.closedPoint k), fun h _ => h⟩

/-- Degree-zero line-bundle classes agree with the degree-zero Picard sheaf at `Spec k`. -/
def picardDegreeZeroEquivAtBase :
    Stacks.Picard.ofSchemeDegreeZero k (B.inclusion.map g) hdim ≃+
      degreeZeroAddSubgroup B hX hk g hdim (terminalTest B hk) where
  toFun c := ⟨ofSchemeAddEquivPicardFunctorOfCurve B hX k g c.1,
    (mem_degreeZeroAtBase_iff B hX hk g hdim c.1).mpr c.2⟩
  invFun ξ := ⟨(ofSchemeAddEquivPicardFunctorOfCurve B hX k g).symm ξ.1, by
    apply (mem_degreeZeroAtBase_iff B hX hk g hdim _).mp
    rw [AddEquiv.apply_symm_apply]
    exact ξ.2⟩
  left_inv c := Subtype.ext (AddEquiv.symm_apply_apply _ _)
  right_inv ξ := Subtype.ext (AddEquiv.apply_symm_apply _ _)
  map_add' c d := Subtype.ext (map_add (ofSchemeAddEquivPicardFunctorOfCurve B hX k g) c.1 d.1)

/-- The terminal test scheme is the tensor unit `Spec k` over `Spec k`. -/
def unitIsoTerminalTest :
    𝟙_ (Over (Spec (.of k))) ≅
      (BigFppfOver.toOver B (Spec (.of k)) hk).obj (terminalTest B hk) :=
  { hom := Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ B.inclusion.map (𝟙 (B.obj hk)) = 𝟙 _
      rw [CategoryTheory.Functor.map_id, Category.comp_id])
    inv := Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ 𝟙 _ = B.inclusion.map (𝟙 (B.obj hk))
      rw [CategoryTheory.Functor.map_id, Category.comp_id])
    hom_inv_id := Over.OverMorphism.ext (Category.comp_id _)
    inv_hom_id := Over.OverMorphism.ext (Category.comp_id _) }

variable {J : Grp (Over (Spec (.of k)))} (hJ : IsJacobianOf B hX hk g hdim J)

/-- For every Jacobian representer, degree-zero Picard classes are its `k`-points. -/
def IsJacobianOf.picardDegreeZeroEquivPoints :
    Stacks.Picard.ofSchemeDegreeZero k (B.inclusion.map g) hdim ≃+
      Additive (𝟙_ (Over (Spec (.of k))) ⟶ J.X) :=
  (picardDegreeZeroEquivAtBase B hX hk g hdim).trans
    ((hJ.homMulEquiv (terminalTest B hk)).symm.toAdditive.trans
      (homMulEquivOfIso (unitIsoTerminalTest B hk)).toAdditive)

/-- For every geometric Jacobian, all nonzero-order Picard torsion is the torsion of
its rational points. Stacks proves that torsion has degree zero. -/
def IsJacobianOf.picardTorsionEquivPoints [IsCommMonObj J.X] {m : ℤ} (hm : m ≠ 0) :
    AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) m ≃+
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J.X)) m :=
  (Stacks.Picard.addSubgroupTorsionByAddEquivSubmodule (Stacks.Picard.ofScheme X) m).trans
    ((Stacks.Picard.torsionByOfSchemeAddEquivPoints (B.inclusion.map g) hdim
      (hJ.picardDegreeZeroEquivPoints B hX hk g hdim) hm).trans
        (Stacks.Picard.addSubgroupTorsionByAddEquivSubmodule
          (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J.X)) m).symm)

end ArithmeticOfJacobiPolynomials.Jacobian
