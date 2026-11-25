/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticPicardTorsion
public import ArithmeticOfJacobiPolynomials.Geometry.Jacobian.Points

/-!
# Branch differences generate the Jacobian two-torsion

The manuscript's branch description (§6.5) follows by composing the
proved branch maps with the canonical Picard-to-Jacobian point equivalence.
The Jacobian is any representer of the degree-zero relative Picard sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace ArithmeticOfJacobiPolynomials.Hyperelliptic

variable {k : Type u} [Field k] [IsAlgClosed k] {f : k[X]}
  (B : BigFppfSite.{u}) (hX : B.Contains (projectiveModel f))
  (hk : B.Contains (Spec (.of k))) (g : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
  [Smooth (B.inclusion.map g)] [IsProper (B.inclusion.map g)]
  (hdim : topologicalKrullDim (projectiveModel f) ≤ 1)
  {J : Grp (Over (Spec (.of k)))} [IsCommMonObj J.X]
  (hJ : Jacobian.IsJacobianOf B hX hk g hdim J)

/-- Finite branch differences, interpreted as points of the Jacobian. -/
def branchJacobianTwoTorsionHom (h2 : (2 : k) ≠ 0) (hf : f.Separable) (c₀ : BranchRoot f) :
    (BranchRoot f → ZMod 2) →+
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J.X)) (2 : ℤ) :=
  (hJ.picardTorsionEquivPoints B hX hk g hdim (by norm_num : (2 : ℤ) ≠ 0)).toAddMonoidHom.comp
    ((branchTorsionHom h2 hf c₀).codRestrict _ fun v =>
      (AddSubgroup.torsionBy.nsmul_iff (n := 2)).mpr
        (two_nsmul_branchTorsionHom h2 hf c₀ v))

/-- In even degree, every Jacobian two-torsion point comes from branch differences. -/
theorem surjective_branchJacobianTwoTorsionHom (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hsplit : f.roots.card = f.natDegree) (heven : Even f.natDegree) (c₀ : BranchRoot f) :
    Function.Surjective (branchJacobianTwoTorsionHom B hX hk g hdim hJ h2 hf c₀) := by
  intro a
  let e := hJ.picardTorsionEquivPoints B hX hk g hdim (by norm_num : (2 : ℤ) ≠ 0)
  have ha : (e.symm a).1 ∈ (branchTorsionHom h2 hf c₀).range := by
    rw [range_branchTorsionHom_eq_twoTorsion h2 hf hsplit heven c₀]
    exact (e.symm a).2
  obtain ⟨v, hv⟩ := ha
  refine ⟨v, ?_⟩
  change e _ = a
  rw [← e.apply_symm_apply a]
  congr 1
  exact Subtype.ext hv

/-- Branch differences based at infinity, interpreted as Jacobian points. -/
def branchJacobianTwoTorsionHomInf (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (hodd : Odd f.natDegree) :
    (BranchRoot f → ZMod 2) →+
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J.X)) (2 : ℤ) :=
  (hJ.picardTorsionEquivPoints B hX hk g hdim (by norm_num : (2 : ℤ) ≠ 0)).toAddMonoidHom.comp
    ((branchTorsionHomInf (eval_zero_reflect_of_odd hodd) h2 hf hdeg).codRestrict _ fun v =>
      (AddSubgroup.torsionBy.nsmul_iff (n := 2)).mpr
        (two_nsmul_branchTorsionHomInf (eval_zero_reflect_of_odd hodd) h2 hf hdeg v))

/-- In odd degree, every Jacobian two-torsion point comes from branch differences. -/
theorem surjective_branchJacobianTwoTorsionHomInf (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (hsplit : f.roots.card = f.natDegree) (hodd : Odd f.natDegree) :
    Function.Surjective (branchJacobianTwoTorsionHomInf B hX hk g hdim hJ h2 hf hdeg hodd) := by
  intro a
  let e := hJ.picardTorsionEquivPoints B hX hk g hdim (by norm_num : (2 : ℤ) ≠ 0)
  have ha : (e.symm a).1 ∈
      (branchTorsionHomInf (eval_zero_reflect_of_odd hodd) h2 hf hdeg).range := by
    rw [range_branchTorsionHomInf_eq_twoTorsion h2 hf hdeg hsplit hodd]
    exact (e.symm a).2
  obtain ⟨v, hv⟩ := ha
  refine ⟨v, ?_⟩
  change e _ = a
  rw [← e.apply_symm_apply a]
  congr 1
  exact Subtype.ext hv

end ArithmeticOfJacobiPolynomials.Hyperelliptic
